// #include <bits/allocator.h> // Temp fix for gcc13 global pragma
// #pragma GCC target("avx2,bmi2,popcnt,lzcnt")
// #pragma GCC optimize("O3,unroll-loops")
#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
#endif
#ifdef LOCAL
	#include "Debug.h"
#else
	#define debug_endl() 42
	#define debug(...) 42
	#define debug2(...) 42
	#define debug_bin(...) 42
#endif

template<class T>
struct graph{
	using Weight_t = T;
	struct Edge_t{
		int from, to;
		T cost;
		Edge_t &inplace_flip(){
			swap(from, to);
			return *this;
		}
		Edge_t flip() const{
			return (*this).inplace_flip();
		}
	};
	int n;
	vector<Edge_t> edge;
	vector<vector<int>> adj;
	function<bool(int)> ignore;
	graph(int n = 1): n(n), adj(n){
		assert(n >= 1);
	}
	graph(const vector<vector<int>> &adj, bool undirected = true): n((int)adj.size()), adj(n){
		assert(n >= 1);
		if(undirected){
			for(auto u = 0; u < n; ++ u) for(auto v: adj[u]) if(u < v) link(u, v);
		}
		else for(auto u = 0; u < n; ++ u) for(auto v: adj[u]) orient(u, v);
	}
	graph(const vector<vector<pair<int, T>>> &adj, bool undirected = true): n((int)adj.size()), adj(n){
		assert(n >= 1);
		if(undirected){
			for(auto u = 0; u < n; ++ u) for(auto [v, w]: adj[u]) if(u < v) link(u, v, w);
		}
		else for(auto u = 0; u < n; ++ u) for(auto [v, w]: adj[u]) orient(u, v, w);
	}
	graph(int n, vector<array<int, 2>> &edge, bool undirected = true): n(n), adj(n){
		assert(n >= 1);
		for(auto [u, v]: edge) undirected ? link(u, v) : orient(u, v);
	}
	graph(int n, vector<tuple<int, int, T>> &edge, bool undirected = true): n(n), adj(n){
		assert(n >= 1);
		for(auto [u, v, w]: edge) undirected ? link(u, v, w) : orient(u, v, w);
	}
	int add_vertex(){
		adj.emplace_back();
		return n ++;
	}
	int operator()(int u, int id) const{
		#ifdef LOCAL
		assert(0 <= id && id < (int)edge.size());
		assert(edge[id].from == u || edge[id].to == u);
		#endif
		return u ^ edge[id].from ^ edge[id].to;
	}
	int link(int u, int v, T w = {}){ // insert an undirected edge
		int id = (int)edge.size();
		adj[u].push_back(id), adj[v].push_back(id), edge.push_back({u, v, w});
		return id;
	}
	int orient(int u, int v, T w = {}){ // insert a directed edge
		int id = (int)edge.size();
		adj[u].push_back(id), edge.push_back({u, v, w});
		return id;
	}
	vector<int> neighbor(int u, int exclude = -1) const{
		vector<int> res;
		for(auto id: adj[u]){
			if(id == exclude || ignore && ignore(id)) continue;
			res.push_back(operator()(u, id));
		}
		return res;
	}
	vector<pair<int, T>> weighted_neighbor(int u, int exclude = -1) const{
		vector<pair<int, T>> res;
		for(auto id: adj[u]){
			if(id == exclude || ignore && ignore(id)) continue;
			res.push_back({operator()(u, id), edge[id].cost});
		}
		return res;
	}
	void clear(){
		for(auto [u, v, w]: edge){
			adj[u].clear();
			adj[v].clear();
		}
		edge.clear();
		ignore = {};
	}
	graph transpose() const{ // the transpose of the directed graph
		graph res(n);
		for(auto id = 0; id < (int)edge.size(); ++ id){
			if(ignore && ignore(id)) continue;
			res.orient(edge[id].to, edge[id].from, edge[id].cost);
		}
		return res;
	}
	int degree(int u) const{ // the degree (outdegree if directed) of u (without the ignoration rule)
		return (int)adj[u].size();
	}
	// The adjacency list is sorted for each vertex.
	vector<vector<int>> get_adjacency_list() const{
		vector<vector<int>> res(n);
		for(auto u = 0; u < n; ++ u) for(auto id: adj[u]){
			if(ignore && ignore(id)) continue;
			res[(*this)(u, id)].push_back(u);
		}
		return res;
	}
	void set_ignoration_rule(const function<bool(int)> &f){
		ignore = f;
	}
	void reset_ignoration_rule(){
		ignore = nullptr;
	}
	friend ostream &operator<<(ostream &out, const graph &g){
		for(auto id = 0; id < (int)g.edge.size(); ++ id){
			if(g.ignore && g.ignore(id)) continue;
			auto &e = g.edge[id];
			out << "{" << e.from << ", " << e.to << ", " << e.cost << "}\n";
		}
		return out;
	}
};

// Requires graph
template<class T, int level>
struct dfs_forest{
	static_assert(0 <= level && level <= 2);
	int n;
	vector<int> pv;
	vector<int> pe;
	vector<int> order;
	vector<int> pos;
	vector<int> end;
	vector<int> size;
	vector<int> depth;
	vector<int> root_of;
	vector<int> root;
	vector<T> dist;
	vector<int> min_depth;
	vector<int> min_depth_origin;
	vector<int> min_depth_spanning_edge;
	// extra_edge[u]: adjacent edges of u which is not part of the spanning forest found during the last dfs-like run.
	vector<vector<int>> extra_edge;
	vector<int> was;
	void init(int n){
		this->n = n;
		pv.resize(n, -1);
		pe.resize(n, -1);
		if constexpr(level >= 2) for(auto u: order){
			extra_edge[u].clear();
			extra_edge[u].shrink_to_fit();
		}
		order.clear();
		pos.resize(n, -1);
		end.resize(n, -1);
		size.resize(n, 0);
		depth.resize(n, -1);
		if constexpr(level >= 1){
			root_of.resize(n, -1);
			root.clear();
			dist.resize(n);
		}
		if constexpr(level >= 2){
			min_depth.resize(n, -1);
			min_depth_origin.resize(n, -1);
			min_depth_spanning_edge.resize(n, -1);
			extra_edge.resize(n, {});
		}
		was.resize(n, -2);
	}
	int attempt = -1;
	// O(# of nodes reachable from u)
	template<class U, class F>
	void _dfs(const graph<U> &g, int u, F UT, T base_dist){
		depth[u] = 0;
		pv[u] = pe[u] = -1;
		if constexpr(level >= 1){
			dist[u] = base_dist;
			root_of[u] = u;
			root.push_back(u);
		}
		auto recurse = [&](auto self, int u)->void{
			was[u] = attempt;
			pos[u] = (int)order.size();
			order.push_back(u);
			size[u] = 1;
			if constexpr(level >= 2){
				min_depth[u] = depth[u];
				min_depth_origin[u] = u;
				min_depth_spanning_edge[u] = -1;
				extra_edge[u].clear();
			}
			for(auto id: g.adj[u]){
				if(id == pe[u] || g.ignore && g.ignore(id)) continue;
				int v = g(u, id);
				if(was[v] == attempt){
					if constexpr(level >= 2){
						if(min_depth[u] > depth[v]){
							min_depth[u] = depth[v];
							min_depth_spanning_edge[u] = id;
						}
						if(pe[v] != id) extra_edge[u].push_back(id);
					}
					continue;
				}
				depth[v] = depth[u] + 1;
				pv[v] = u;
				pe[v] = id;
				if constexpr(level >= 1){
					dist[v] = UT(g.edge[id].cost, dist[u]);
					root_of[v] = root_of[u];
				}
				self(self, v);
				size[u] += size[v];
				if constexpr(level >= 2) if(min_depth[u] > min_depth[v]){
					min_depth[u] = min_depth[v];
					min_depth_origin[u] = min_depth_origin[v];
					min_depth_spanning_edge[u] = min_depth_spanning_edge[v];
				}
			}
			end[u] = (int)order.size();
		};
		recurse(recurse, u);
	}
	// O(# of nodes reachable from src)
	template<class U, class F = plus<>>
	void dfs(const graph<U> &g, const vector<int> &src, F UT = plus<>(), T base_dist = T{}){
		init(g.n);
		++ attempt;
		for(auto u: src){
			assert(0 <= u && u < n);
			if(was[u] != attempt) _dfs(g, u, UT, base_dist);
		}
	}
	// O(n + m)
	template<class U, class F = plus<>>
	void dfs_all(const graph<U> &g, F UT = plus<>(), T base_dist = T{}){
		init(g.n);
		++ attempt;
		for(auto u = 0; u < n; ++ u) if(was[u] != attempt) _dfs(g, u, UT, base_dist);
	}
	// Check if u is visited during the last dfs-like call.
	bool visited(int u) const{
		assert(0 <= u && u < n);
		return was[u] == attempt;
	}
	// Check if u is an ancestor of v in some spanning tree.
	bool ancestor_of(int u, int v) const{
		assert(visited(u) && visited(v));
		return pos[u] <= pos[v] && end[v] <= end[u];
	}
	vector<int> get_path(int u, int v) const{
		assert(visited(u) && visited(v));
		vector<int> left, right;
		while(u != v && ~pv[u] && ~pv[v]){
			if(depth[u] >= depth[v]){
				left.push_back(u);
				u = pv[u];
			}
			else{
				right.push_back(v);
				v = pv[v];
			}
		}
		assert(u == v);
		left.push_back(u);
		left.insert(left.end(), right.rbegin(), right.rend());
		return left;
	}
	// Check if any cycle is found during the last dfs-like call.
	// If must_contain_root = true, the sought cycle is forced to contain one of the root of the trees.
	template<class U>
	optional<pair<int, vector<int>>> find_any_cycle(const graph<U> &g, bool must_contain_root = false) const{
		static_assert(level >= 2);
		for(auto u: order) for(auto id: extra_edge[u]){
			int v = g(u, id);
			if(!ancestor_of(v, u) || must_contain_root && root_of[v] != v) continue;
			vector<int> cycle_edge;
			while(u != v) cycle_edge.push_back(pe[u]), u = pv[u];
			reverse(cycle_edge.begin(), cycle_edge.end());
			cycle_edge.push_back(id);
			return pair{v, cycle_edge};
		}
		return {};
	}
};

// pv, pe, order, pos, end, size, depth
template<class T>
auto make_basic_dfs_forest(){
	return dfs_forest<T, 0>();
}
// (basic_set), root_of, root, dist
template<class T>
auto make_augmented_dfs_forest(){
	return dfs_forest<T, 1>();
}
// (augmented_set), min_depth, min_depth_origin, min_depth_spanning_edge, extra_edge
template<class T>
auto make_full_dfs_forest(){
	return dfs_forest<T, 2>();
}

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n, qn;
	cin >> n >> qn;
	vector<long long> a(n);
	copy_n(istream_iterator<long long>(cin), n, a.begin());
	graph<int> g(n);
	auto df = make_augmented_dfs_forest<int>();
	vector<int> is_root(n, true);
	auto connected = [&](int u, int v)->bool{
		df.dfs(g, {u});
		return df.visited(v);
	};
	auto find_root = [&](int u)->int{
		df.dfs(g, {u});
		for(auto v: df.order){
			if(is_root[v]){
				return v;
			}
		}
		assert(false);
	};
	for(auto qi = 0; qi < qn; ++ qi){
		string op;
		cin >> op;
		if(op == "link"){
			int u, v;
			cin >> u >> v;
			assert(!connected(u, v));
			is_root[find_root(v)] = false;
			g.link(u, v);
		}
		else if(op == "cut"){
			int u, v;
			cin >> u >> v;
			assert(connected(u, v));
			df.dfs(g, {find_root(u)});
			if(df.depth[u] > df.depth[v]){
				swap(u, v);
			}
			vector<array<int, 2>> edge;
			for(auto [u, v, w]: g.edge){
				edge.push_back({u, v});
			}
			g.clear();
			erase(edge, array{u, v});
			erase(edge, array{v, u});
			for(auto [u, v]: edge){
				g.link(u, v);
			}
			is_root[v] = true;
		}
		else if(op == "reroot"){
			int u;
			cin >> u;
			is_root[find_root(u)] = false;
			is_root[u] = true;
		}
		else if(op == "root_of"){
			int u;
			cin >> u;
			cout << find_root(u) << "\n";
		}
		else if(op == "parent_or_is_root"){
			int u;
			cin >> u;
			df.dfs(g, {find_root(u)});
			cout << df.pv[u] << "\n";
		}
		else if(op == "lca_or_disconnected"){
			int u, v;
			cin >> u >> v;
			df.dfs(g, {find_root(u)});
			if(!df.visited(v)){
				cout << "-1\n";
				continue;
			}
			while(u != v){
				if(df.depth[u] >= df.depth[v]){
					u = df.pv[u];
				}
				else{
					v = df.pv[v];
				}
			}
			cout << u << "\n";
		}
		else if(op == "adjacent"){
			int u, v;
			cin >> u >> v;
			auto a = g.neighbor(u);
			if(ranges::find(a, v) != a.end()){
				cout << "1\n";
			}
			else{
				cout << "0\n";
			}
		}
		else if(op == "depth"){
			int u;
			cin >> u;
			df.dfs(g, {find_root(u)});
			cout << df.depth[u] << "\n";
		}
		else if(op == "distance"){
			int u, v;
			cin >> u >> v;
			assert(connected(u, v));
			df.dfs(g, {u});
			cout << df.depth[v] << "\n";
		}
		else if(op == "connected"){
			int u, v;
			cin >> u >> v;
			cout << connected(u, v) << "\n";
		}
		else if(op == "find_ancestor_by_order"){
			int u, k;
			cin >> u >> k;
			df.dfs(g, {find_root(u)});
			assert(df.depth[u] >= k);
			while(k --){
				u = df.pv[u];
			}
			cout << u << "\n";
		}
		else if(op == "find_vertex_by_order"){
			int u, v, k;
			cin >> u >> v >> k;
			df.dfs(g, {v});
			assert(df.depth[u] >= k);
			while(k --){
				u = df.pv[u];
			}
			cout << u << "\n";
		}
		else if(op == "query"){
			int u;
			cin >> u;
			cout << a[u] << "\n";
		}
		else if(op == "query_path"){
			int u, v;
			cin >> u >> v;
			assert(connected(u, v));
			df.dfs(g, {v});
			long long res = a[u];
			while(u != v){
				u = df.pv[u];
				res += a[u];
			}
			cout << res << "\n";
		}
		else if(op == "query_subtree"){
			int u;
			cin >> u;
			df.dfs(g, {find_root(u)});
			long long res = 0;
			for(auto i = df.pos[u]; i < df.end[u]; ++ i){
				res += a[df.order[i]];
			}
			cout << res << "\n";
		}
		else if(op == "set"){
			int u, x;
			cin >> u >> x;
			a[u] = x;
		}
		else if(op == "update"){
			int u, f;
			cin >> u >> f;
			a[u] += f;
		}
		else if(op == "update_path"){
			int u, v, f;
			cin >> u >> v >> f;
			assert(connected(u, v));
			df.dfs(g, {v});
			a[u] += f;
			while(u != v){
				u = df.pv[u];
				a[u] += f;
			}
		}
		else if(op == "update_subtree"){
			int u, f;
			cin >> u >> f;
			df.dfs(g, {find_root(u)});
			for(auto i = df.pos[u]; i < df.end[u]; ++ i){
				a[df.order[i]] += f;
			}
		}
		else if(op == "partition_point"){
			int u, v;
			long long x;
			cin >> u >> v >> x;
			df.dfs(g, {v});
			vector<long long> path{a[u]};
			while(u != v){
				u = df.pv[u];
				path.push_back(a[u]);
			}
			assert(ranges::is_sorted(path));
			cout << ranges::lower_bound(path, x) - path.begin() << "\n";
		}
		else if(op == "max_pref"){
			int u, v;
			long long x;
			cin >> u >> v >> x;
			assert(0 < x);
			df.dfs(g, {v});
			vector<long long> path{0, a[u]};
			while(u != v){
				u = df.pv[u];
				path.push_back(a[u]);
			}
			for(auto i = 1; i < (int)path.size(); ++ i){
				path[i] += path[i - 1];
			}
			int r = 0;
			while(r + 1 < (int)path.size() && path[r + 1] < x){
				++ r;
			}
			cout << r << "\n";
		}
		else{
			assert(false);
		}
	}
	return 0;
}

/*

*/
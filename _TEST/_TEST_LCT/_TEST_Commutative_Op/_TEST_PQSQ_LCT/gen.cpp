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
mt19937 rng(chrono::high_resolution_clock::now().time_since_epoch().count());
mt19937_64 rngll(chrono::high_resolution_clock::now().time_since_epoch().count());
using randint_t = uniform_int_distribution<int>;
using randll_t = uniform_int_distribution<long long>;
using randd_t = uniform_real_distribution<double>;
// return x with probability p, y with probability 1-p
template<class T>
T pick(T x, T y, double p = 0.5){
	assert(-0.0001 <= p && p <= 1.0001);
	return randd_t(0, 1)(rng) <= p ? x : y;
}
array<int, 2> gen_range(int n, bool allow_empty_range = false){
	if(allow_empty_range){
		int l = rng() % (n + 1), r = rng() % (n + 1);
		if(l > r) swap(l, r);
		return {l, r};
	}
	else{
		int l = rng() % n, r = rng() % n;
		if(l > r) swap(l, r);
		return {l, r + 1};
	}
}
template<class T>
vector<T> sample_array(int n, T low, T high, bool distinct = false){
	assert(low < high && (!distinct || high - low >= n));
	set<T> used;
	vector<T> array(n);
	for(auto i = 0; i < n; ++ i){
		T x = randll_t(low, high - 1)(rng);
		if(distinct){
			if(used.count(x)){
				-- i;
				continue;
			}
			used.insert(x);
		}
		array[i] = x;
	}
	return array;
}

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
	// int n = 4, qn = 10, mx = 10;
	int n = rng() % 100 + 2, qn = 10000, mx = 1000;
	cout << n << " " << qn << "\n";
	vector<long long> a(n);
	for(auto i = 0; i < n; ++ i){
		cout << (a[i] = rng() % mx) << " ";
	}
	cout << "\n";
	auto gen_int = [&](long long l, long long r)->long long{
		return uniform_int_distribution<long long>(l, r)(rng);
	};
	vector<string> op_list{
		"link", "link", "link", "link", "link", "link", "link", "link", "link", "link",
		"cut",
		"reroot",
		"root_of",
		"parent_or_is_root",
		"lca_or_disconnected",
		"adjacent",
		"depth",
		"distance",
		"connected",
		"find_ancestor_by_order",
		"find_vertex_by_order",
		"query",
		"query_path",
		"query_subtree",
		"set",
		//"update",
		//"update_path",
		//"update_subtree",
		"partition_point",
		"max_pref",
	};
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
		string op = op_list[rng() % (int)op_list.size()];
		if(op == "link"){
			int u = gen_int(0, n - 2);
			int v = gen_int(u + 1, n - 1);
			if(rng() % 2){
				swap(u, v);
			}
			if(connected(u, v)){
				-- qi;
				continue;
			}
			cout << op << " " << u << " " << v << "\n";
			is_root[find_root(v)] = false;
			g.link(u, v);
		}
		else if(op == "cut"){
			if(g.edge.empty()){
				-- qi;
				continue;
			}
			auto [u, v, _] = g.edge[rng() % (int)g.edge.size()];
			cout << op << " " << u << " " << v << "\n";
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
			int u = rng() % n;
			cout << op << " " << u << "\n";
			is_root[find_root(u)] = false;
			is_root[u] = true;
		}
		else if(op == "root_of"){
			int u = rng() % n;
			cout << op << " " << u << "\n";
		}
		else if(op == "parent_or_is_root"){
			cout << op << " " << rng() % n << "\n";
		}
		else if(op == "lca_or_disconnected"){
			cout << op << " " << rng() % n << " " << rng() % n << "\n";
		}
		else if(op == "adjacent"){
			cout << op << " " << rng() % n << " " << rng() % n << "\n";
		}
		else if(op == "depth"){
			cout << op << " " << rng() % n << "\n";
		}
		else if(op == "distance"){
			int u = rng() % n, v = rng() % n;
			if(!connected(u, v)){
				-- qi;
				continue;
			}
			cout << op << " " << u << " " << v << "\n";
		}
		else if(op == "connected"){
			cout << op << " " << rng() % n << " " << rng() % n << "\n";
		}
		else if(op == "find_ancestor_by_order"){
			int u = rng() % n;
			df.dfs(g, {find_root(u)});
			cout << op << " " << u << " " << rng() % (df.depth[u] + 1) << "\n";
		}
		else if(op == "find_vertex_by_order"){
			int u = rng() % n, v = rng() % n;
			if(!connected(u, v)){
				-- qi;
				continue;
			}
			df.dfs(g, {v});
			cout << op << " " << u << " " << v << " " << rng() % (df.depth[u] + 1) << "\n";
		}
		else if(op == "query"){
			cout << op << " " << rng() % n << "\n";
		}
		else if(op == "query_path"){
			int u = rng() % n, v = rng() % n;
			if(!connected(u, v)){
				-- qi;
				continue;
			}
			cout << op << " " << u << " " << v << "\n";
		}
		else if(op == "query_subtree"){
			cout << op << " " << rng() % n << "\n";
		}
		else if(op == "set"){
			int u = rng() % n, x = rng() % mx;
			cout << op << " " << u << " " << x << "\n";
			a[u] = x;
		}
		else if(op == "update"){
			int u = rng() % n, f = rng() % mx;
			cout << op << " " << u << " " << f << "\n";
			a[u] += f;
		}
		else if(op == "update_path"){
			int u = rng() % n, v = rng() % n, f = rng() % mx;
			if(!connected(u, v)){
				-- qi;
				continue;
			}
			cout << op << " " << u << " " << v << " " << f << "\n";
			df.dfs(g, {v});
			a[u] += f;
			while(u != v){
				u = df.pv[u];
				a[u] += f;
			}
		}
		else if(op == "update_subtree"){
			int u = rng() % n, f = rng() % mx;
			cout << op << " " << u << " " << f << "\n";
			df.dfs(g, {find_root(u)});
			for(auto i = df.pos[u]; i < df.end[u]; ++ i){
				a[df.order[i]] += f;
			}
		}
		else if(op == "partition_point"){
			int u = rng() % n, v = rng() % n;
			if(!connected(u, v)){
				-- qi;
				continue;
			}
			df.dfs(g, {v});
			vector<long long> path{a[u]};
			while(u != v){
				u = df.pv[u];
				path.push_back(a[u]);
			}
			if(!ranges::is_sorted(a)){
				-- qi;
				continue;
			}
			cout << op << " " << u << " " << v << " " << gen_int(a.front(), a.back()) << "\n";
		}
		else if(op == "max_pref"){
			int u = rng() % n, v = rng() % n;
			if(!connected(u, v)){
				-- qi;
				continue;
			}
			cout << op << " " << u << " " << v << " " << rng() % (4LL * mx) + 1 << "\n";
		}
		else{
			assert(false);
		}
	}
	return 0;
}

/*
- link(u, v): link two nodes which does not lie in the same CC
- cut(u, v): cut the edge between u and v. This query is only given when there is an edge connecting them.
- reroot(u): Make u the root of its CC
- parent_or_is_root(u): if u is the root, return -1, otherwise return the parent of u
- lca_or_disconnected(u, v): if u and v lies in the same cc, returns their LCA, otherwise, returns -1
- adjacent(u, v): returns whether there is an edge between u and v
- depth(u): returns the depth from the root of cc containing u, to u
- distance(u, v): returns the distance between u and v
- connected(u, v): returns whether u and v lies in the same CC
- find_ancestor_by_order(u, k): find the k-th ancestor of u, where u itself is 0-th ancestor
- find_vertex_by_order(u, v, k): find the k-th node on the u-v path, where u itself is 0-th vertex. This is only given when k is equal or less than the distance between u and v
- query(u): returns data[u]
- query_path(u, v): returns the aggregation of data on the u-v path
- query_subtree(u): returns the aggregation of data on the subtree of u
- set(u, x): set data[u] <- x
- update(u, f): update data[u] by f
- update_path(u, v, f): update all data on u-v path by f
- update_subtree(u, f): update all data on subtree of u by f
- partiiton_point(u, v, pred)
- max_pref(u, v, pred)
*/
// #pragma GCC optimize("O3,unroll-loops")
#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
#endif

template<bool HAS_QUERY, bool HAS_UPDATE, class T, class U, class F1, class F2, class F3>
struct segment_tree_persistent_base{
	static_assert(HAS_QUERY || HAS_UPDATE);
#define ifQ if constexpr(HAS_QUERY)
#define ifU if constexpr(HAS_UPDATE)
	int n;
	vector<int> left; // left child
	vector<int> right; // right child
	vector<T> data;
	vector<U> data_action;
	F1 TT; // monoid operation (always adjacent)
	T T_id; // monoid identity
	F2 UU; // monoid operation (superset, subset)
	U U_id; // monoid identity
	F3 UT; // action of U on T (superset, subset)
	// O(n)
	segment_tree_persistent_base(F1 TT, T T_id, F2 UU, U U_id, F3 UT): TT(TT), T_id(T_id), UU(UU), U_id(U_id), UT(UT){ }
	segment_tree_persistent_base &operator=(const segment_tree_persistent_base &seg){
		n = seg.n;
		left = seg.left;
		right = seg.right;
		data = seg.data;
		data_action = seg.data_action;
		return *this;
	}
	int _last_state() const{
		return (int)data.size() - 1;
	}
	int _new_state(int l, int r, T x){
		static_assert(HAS_QUERY);
		left.push_back(l);
		right.push_back(r);
		data.push_back(x);
		ifU data_action.push_back(U_id);
		return _last_state();
	}
	int _new_state(int l, int r, T x, U f){
		static_assert(HAS_QUERY && HAS_UPDATE);
		left.push_back(l);
		right.push_back(r);
		data.push_back(x);
		data_action.push_back(f);
		return _last_state();
	}
	int _new_state_action(int l, int r, U f){
		static_assert(!HAS_QUERY && HAS_UPDATE);
		left.push_back(l);
		right.push_back(r);
		ifU data_action.push_back(f);
		return _last_state();
	}
	int copy(int u){
		assert(0 <= u && u <= _last_state());
		left.push_back(left[u]);
		right.push_back(right[u]);
		ifQ data.push_back(data[u]);
		ifU data_action.push_back(data_action[u]);
		return _last_state();
	}
	// Invalidates all previous roots
	// O(n)
	int build(int n){
		static_assert(HAS_QUERY);
		return build(vector<T>(n, T_id));
	}
	// Invalidates all previous roots
	// O(n)
	int build(int n, T x){
		static_assert(HAS_QUERY);
		return build(vector<T>(n, x));
	}
	// Invalidates all previous roots
	// O(n)
	int build(const vector<T> &a){
		static_assert(HAS_QUERY);
		assert(!a.empty());
		n = (int)a.size();
		left.clear();
		right.clear();
		data.clear();
		data_action.clear();
		auto recurse = [&](auto self, int l, int r)->int{
			if(r - l == 1) return _new_state(-1, -1, a[l]);
			int m = l + (r - l >> 1);
			int v = self(self, l, m), w = self(self, m, r);
			return _new_state(v, w, TT(data[v], data[w]));
		};
		return recurse(recurse, 0, n);
	}
	int build_action(int n){
		static_assert(!HAS_QUERY && HAS_UPDATE);
		return build_action(vector<U>(n, U_id));
	}
	int build_action(int n, U f){
		static_assert(!HAS_QUERY && HAS_UPDATE);
		return build_action(vector<U>(n, f));
	}
	int build_action(const vector<U> &a){
		static_assert(!HAS_QUERY && HAS_UPDATE);
		assert(!a.empty());
		n = (int)a.size();
		left.clear();
		right.clear();
		data.clear();
		data_action.clear();
		auto recurse = [&](auto self, int l, int r)->int{
			if(r - l == 1) return _new_state_action(-1, -1, a[l]);
			int m = l + (r - l >> 1);
			int v = self(self, l, m), w = self(self, m, r);
			return _new_state_action(v, w, U_id);
		};
		return recurse(recurse, 0, n);
	}
	int _push_copy(int u){
		static_assert(HAS_UPDATE);
		if(data_action[u] == U_id) return copy(u);
		int v_new = copy(left[u]), w_new = copy(right[u]);
		ifQ data[v_new] = UT(data_action[u], data[v_new]);
		data_action[v_new] = UU(data_action[u], data_action[v_new]);
		ifQ data[w_new] = UT(data_action[u], data[w_new]);
		data_action[w_new] = UU(data_action[u], data_action[w_new]);
		ifQ u = _new_state(v_new, w_new, TT(data[v_new], data[w_new]));
		else u = _new_state_action(v_new, w_new, UU(data_action[v_new], data_action[w_new]));
		data_action[u] = U_id;
		return u;
	}
	// Assumes u represents an interval of size n
	// O(log(n))
	pair<int, T> query(int u, int p){	
		static_assert(HAS_QUERY);
		assert(0 <= u && u <= _last_state());
		assert(0 <= p && p < n);
		ifU{
			auto recurse = [&](auto self, int u, int l, int r)->pair<int, T>{
				if(r - l == 1) return {u, data[u]};
				u = _push_copy(u);
				int m = l + (r - l >> 1);
				if(p < m){
					auto [v, x] = self(self, left[u], l, m);
					left[u] = v;
					return {u, x};
				}
				else{
					auto [w, x] = self(self, right[u], m, r);
					right[u] = w;
					return {u, x};
				}
			};
			return recurse(recurse, u, 0, n);
		}
		else{
			int root = u;
			for(auto l = 0, r = n; ; ){
				if(r - l == 1) return {root, data[u]};
				int m = l + (r - l >> 1);
				if(p < m) u = left[u], r = m;
				else u = right[u], l = m;
			}
		}
	}
	// Assumes u represents an interval of size n
	// O(log(n))
	pair<int, U> query_action(int u, int p){
		static_assert(!HAS_QUERY && HAS_UPDATE);
		assert(0 <= u && u <= _last_state());
		assert(0 <= p && p < n);
		auto recurse = [&](auto self, int u, int l, int r)->pair<int, U>{
			if(r - l == 1) return {u, data_action[u]};
			u = _push_copy(u);
			int m = l + (r - l >> 1);
			if(p < m){
				auto [v, f] = self(self, left[u], l, m);
				left[u] = v;
				return {u, f};
			}
			else{
				auto [w, f] = self(self, right[u], m, r);
				right[u] = w;
				return {u, f};
			}
		};
		return recurse(recurse, u, 0, n);
	}
	// Assumes u represents an interval of size n
	// O(log(n))
	pair<int, T> query(int u, int ql, int qr){
		static_assert(HAS_QUERY);
		assert(0 <= u && u <= _last_state());
		assert(0 <= ql && ql <= qr && qr <= n);
		if(ql == qr) return {u, T_id};
		auto recurse = [&](auto self, int u, int l, int r)->pair<int, T>{
			if(qr <= l || r <= ql) return {u, T_id};
			if(ql <= l && r <= qr) return {u, data[u]};
			ifU u = _push_copy(u);
			int m = l + (r - l >> 1);
			auto [v, x] = self(self, left[u], l, m);
			auto [w, y] = self(self, right[u], m, r);
			left[u] = v, right[u] = w;
			return pair{u, TT(x, y)};
		};
		return recurse(recurse, u, 0, n);
	}
	// Assumes u represents an interval of size n
	// O(1)
	pair<int, T> query_all(int u) const{
		static_assert(HAS_QUERY);
		assert(0 <= u && u <= _last_state());
		return {u, data[u]};
	}
	// Assumes u represents an interval of size n
	// O(n)
	pair<int, vector<T>> to_array(int u){
		static_assert(HAS_QUERY);
		assert(0 <= u && u <= _last_state());
		vector<T> res;
		auto recurse = [&](auto self, int u, int l, int r)->int{
			if(r - l == 1){
				res.push_back(data[u]);
				return u;
			}
			ifU u = _push_copy(u);
			int m = l + (r - l >> 1);
			left[u] = self(self, left[u], l, m);
			right[u] = self(self, right[u], m, r);
			return u;
		};
		u = recurse(recurse, u, 0, n);
		return {u, res};
	}
	// Assumes u represents an interval of size n
	// O(n)
	pair<int, vector<U>> to_array_of_updates(int u){
		static_assert(!HAS_QUERY && HAS_UPDATE);
		assert(0 <= u && u <= _last_state());
		vector<U> res;
		auto recurse = [&](auto self, int u, int l, int r)->int{
			if(r - l == 1){
				res.push_back(data_action[u]);
				return u;
			}
			u = _push_copy(u);
			int m = l + (r - l >> 1);
			left[u] = self(self, left[u], l, m);
			right[u] = self(self, right[u], m, r);
			return u;
		};
		u = recurse(recurse, u, 0, n);
		return {u, res};
	}
	// Assumes u represents an interval of size n
	// O(log(n))
	int set(int u, int p, T x){
		static_assert(HAS_QUERY);
		assert(0 <= u && u <= _last_state());
		assert(0 <= p && p < n);
		auto recurse = [&](auto self, int u, int l, int r)->int{
			if(r - l == 1) return _new_state(-1, -1, x);
			int m = l + (r - l >> 1);
			ifU{
				u = _push_copy(u);
				if(p < m) left[u] = self(self, left[u], l, m);
				else right[u] = self(self, right[u], m, r);
				data[u] = TT(data[left[u]], data[right[u]]);
				return u;
			}
			else{
				int v = left[u], w = right[u];
				if(p < m) v = self(self, v, l, m);
				else w = self(self, w, m, r);
				return _new_state(v, w, TT(data[v], data[w]));
			}
		};
		return recurse(recurse, u, 0, n);
	}
	// Assumes u represents an interval of size n
	// O(log(n))
	int set_action(int u, int p, U f){
		static_assert(!HAS_QUERY && HAS_UPDATE);
		assert(0 <= u && u <= _last_state());
		assert(0 <= p && p < n);
		auto recurse = [&](auto self, int u, int l, int r)->int{
			if(r - l == 1) return _new_state_action(-1, -1, f);
			u = _push_copy(u);
			int m = l + (r - l >> 1);
			if(p < m) left[u] = self(self, left[u], l, m);
			else right[u] = self(self, right[u], m, r);
			return u;
		};
		return recurse(recurse, u, 0, n);
	}
	// Assumes u represents an interval of size n
	// O(log(n))
	int update(int u, int p, U f){
		static_assert(HAS_UPDATE);
		assert(0 <= u && u <= _last_state());
		assert(0 <= p && p < n);
		auto recurse = [&](auto self, int u, int l, int r)->int{
			if(r - l == 1){
				ifQ return _new_state(-1, -1, UT(f, data[u]));
				else return _new_state_action(-1, -1, UU(f, data_action[u]));
			}
			u = _push_copy(u);
			int m = l + (r - l >> 1);
			if(p < m) left[u] = self(self, left[u], l, m);
			else right[u] = self(self, right[u], m, r);
			ifQ data[u] = TT(data[left[u]], data[right[u]]);
			return u;
		};
		// return recurse(recurse, u, 0, n);
		u = recurse(recurse, u, 0, n);
		return u;
	}
	// Assumes u represents an interval of size n
	// O(log(n))
	int update(int u, int ql, int qr, U f){
		static_assert(HAS_UPDATE);
		assert(0 <= u && u <= _last_state());
		assert(0 <= ql && ql <= qr && qr <= n);
		if(ql == qr) return u;
		auto recurse = [&](auto self, int u, int l, int r)->int{
			if(qr <= l || r <= ql) return u;
			if(ql <= l && r <= qr){
				ifQ return _new_state(left[u], right[u], UT(f, data[u]), UU(f, data_action[u]));
				else return _new_state_action(left[u], right[u], UU(f, data_action[u]));
			}
			u = _push_copy(u);
			int m = l + (r - l >> 1);
			left[u] = self(self, left[u], l, m);
			right[u] = self(self, right[u], m, r);
			ifQ data[u] = TT(data[left[u]], data[right[u]]);
			return u;
		};
		return recurse(recurse, u, 0, n);
	}
	// pred(sum[l, r)) is T, T, ..., T, F, F, ..., F
	// Returns max r with T
	// Assumes u represents an interval of size n
	// O(log(n))
	pair<int, int> max_pref(int u, int ql, auto pred){
		static_assert(HAS_QUERY);
		assert(0 <= u && u <= _last_state());
		assert(0 <= ql && ql <= n && pred(T_id));
		if(ql == n) return {u, ql};
		T pref = T_id;
		auto recurse = [&](auto self, int u, int l, int r)->pair<int, int>{
			if(r <= ql) return {u, -1};
			if(ql <= l && pred(TT(pref, data[u]))){
				pref = TT(pref, data[u]);
				return {u, -1};
			}
			if(r - l == 1) return {u, l};
			ifU{
				u = _push_copy(u);
				int m = l + (r - l >> 1);
				auto [v, p] = self(self, left[u], l, m);
				left[u] = v;
				if(~p) return {u, p};
				auto [w, q] = self(self, right[u], m, r);
				right[u] = w;
				return {u, q};
			}
			else{
				int m = l + (r - l >> 1), p = self(self, left[u], l, m);
				return ~p ? pair{u, p} : pair{u, self(self, right[u], m, r)};
			}
		};
		auto [v, qr] = recurse(recurse, u, 0, n);
		if(!~qr) qr = n;
		return {v, qr};
	}
	// pred(sum[l, r)) is F, F, ..., F, T, T, ..., T
	// Returns min l with T
	// Assumes u represents an interval of size n
	// O(log(n))
	pair<int, int> min_suff(int u, int qr, auto pred){
		static_assert(HAS_QUERY);
		assert(0 <= u && u <= _last_state());
		assert(0 <= qr && qr <= n && pred(T_id));
		if(qr == 0) return {u, qr};
		T suff = T_id;
		auto recurse = [&](auto self, int u, int l, int r)->pair<int, int>{
			if(qr <= l) return {u, -1};
			if(r <= qr && pred(TT(data[u], suff))){
				suff = TT(data[u], suff);
				return {u, -1};
			}
			if(r - l == 1) return {u, r};
			ifU{
				u = _push_copy(u);
				int m = l + (r - l >> 1);
				auto [w, q] = self(self, right[u], m, r);
				right[u] = w;
				if(~q) return {u, q};
				auto [v, p] = self(self, left[u], l, m);
				left[u] = v;
				return {u, p};
			}
			else{
				int m = l + (r - l >> 1), p = self(self, right[u], m, r);
				return ~p ? pair{u, p} : pair{u, self(self, left[u], l, m)};
			}
		};
		auto [v, ql] = recurse(recurse, u, 0, n);
		if(!~ql) ql = 0;
		return {v, ql};
	}
	// Assumes u represents an interval of size n
	template<class ostream_t>
	int print(ostream_t &out, int u){
		assert(0 <= u && u <= _last_state());
		ifQ{
			auto [v, arr] = to_array(u);
			out << "{";
			for(auto i = 0; i < (int)arr.size(); ++ i){
				out << arr[i];
				if(i + 1 < (int)arr.size()) out << ", ";
			}
			out << "}";
			return v;
		}
		else{
			auto [v, arr] = to_array_of_updates(u);
			out << "{";
			for(auto i = 0; i < (int)arr.size(); ++ i){
				out << arr[i];
				if(i + 1 < (int)arr.size()) out << ", ";
			}
			out << "}";
			return v;
		}
	}
};

// Supports query
template<class T, class F>
auto make_Q_segment_tree_persistent(F TT, T T_id){
	using U = int;
	auto _UU = [&](U, U)->U{ return U{}; };
	auto _UT = [&](U, T)->T{ return T{}; };
	return segment_tree_persistent_base<true, false, T, U, F, decltype(_UU), decltype(_UT)>(TT, T_id, _UU, U{}, _UT);
}
// Supports update
template<class U, class F>
auto make_U_segment_tree_persistent(F UU, U U_id){
	using T = int;
	auto _TT = [&](T, T)->T{ return T{}; };
	auto _UT = [&](U, T)->T{ return T{}; };
	return segment_tree_persistent_base<false, true, T, U, decltype(_TT), F, decltype(_UT)>(_TT, T{}, UU, U_id, _UT);
}
// Supports query and update
template<class T, class U, class F1, class F2, class F3>
auto make_QU_segment_tree_persistent(F1 TT, T T_id, F2 UU, U U_id, F3 UT){
	return segment_tree_persistent_base<true, true, T, U, F1, F2, F3>(TT, T_id, UU, U_id, UT);
}

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n, qn;
	cin >> n >> qn;
	auto seg = make_QU_segment_tree_persistent([&](auto x, auto y){ return max(x, y); }, 0LL, plus<>(), 0LL, plus<>());
	vector<long long> init(n);
	copy_n(istream_iterator<long long>(cin), n, init.begin());
	vector<int> root(qn + 1);
	root[0] = seg.build(init);
	for(auto qi = 0; qi < qn; ++ qi){
		int type, u;
		cin >> type >> u;
		u = root[u];
		auto &v = root[qi + 1];
		if(type == 0){ // copy
			v = seg.copy(u);
		}
		else if(type == 1){ // point query
			int p;
			cin >> p;
			long long x;
			tie(v, x) = seg.query(u, p);
			cout << x << "\n";
		}
		else if(type == 2){ // range query
			int ql, qr;
			cin >> ql >> qr;
			long long x;
			tie(v, x) = seg.query(u, ql, qr);
			cout << x << "\n";
		}
		else if(type == 3){ // all query
			long long x;
			tie(v, x) = seg.query_all(u);
			cout << x << "\n";
		}
		else if(type == 4){ // to_array
			vector<long long> arr;
			tie(v, arr) = seg.to_array(u);
			for(auto i = 0; i < n; ++ i){
				cout << arr[i] << " ";
			}
			cout << "\n";
		}
		else if(type == 5){ // point set
			int p, x;
			cin >> p >> x;
			v = seg.set(u, p, x);
		}
		else if(type == 6){ // point update
			int p, f;
			cin >> p >> f;
			v = seg.update(u, p, f);
		}
		else if(type == 7){ // range update
			int ql, qr, f;
			cin >> ql >> qr >> f;
			v = seg.update(u, ql, qr, f);
		}
		else if(type == 8){ // max pref
			int ql;
			long long th;
			cin >> ql >> th;
			int r;
			tie(v, r) = seg.max_pref(u, ql, [&](auto sum){ return sum <= th; });
			cout << r << "\n";
		}
		else if(type == 9){ // min suff
			int qr;
			long long th;
			cin >> qr >> th;
			int l;
			tie(v, l) = seg.min_suff(u, qr, [&](auto sum){ return sum <= th; });
			cout << l << "\n";
		}
		else{
			assert(false);
		}
	}
	return 0;
}

/*
0 int copy(int u)
1	pair<int, T> query(int u, int p){	
		static_assert(HAS_QUERY);
	pair<int, U> query_action(int u, int p){
		static_assert(!HAS_QUERY && HAS_UPDATE);
2	pair<int, T> query(int u, int ql, int qr){
		static_assert(HAS_QUERY);
3	pair<int, T> query_all(int u) const{
		static_assert(HAS_QUERY);
4	pair<int, vector<T>> to_array(int u){
		static_assert(HAS_QUERY);
	pair<int, vector<U>> to_array_of_updates(int u){
		static_assert(!HAS_QUERY && HAS_UPDATE);
5	int set(int u, int p, T x){
		static_assert(HAS_QUERY);
	int set_action(int u, int p, U f){
		static_assert(!HAS_QUERY && HAS_UPDATE);
6	int update(int u, int p, U f){
		static_assert(HAS_UPDATE);
7	int update(int u, int ql, int qr, U f){
		static_assert(HAS_UPDATE);
8	pair<int, int> max_pref(int u, int ql, auto pred){
		static_assert(HAS_QUERY);
9	pair<int, int> min_suff(int u, int qr, auto pred){
		static_assert(HAS_QUERY);
*/
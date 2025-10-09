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

template<bool HAS_PATH_QUERY, bool HAS_PATH_UPDATE, bool HAS_SUBTREE_QUERY, bool HAS_SUBTREE_UPDATE, bool IS_COMMUTATIVE, class T, class U, class F1, class F2, class F3, class F4, class F5, class F6>
struct link_cut_trees_base{
#ifdef LOCAL
	#define ASSERT(x) assert(x)
#else
	#define ASSERT(x) 42
#endif
#define ifPQ if constexpr(HAS_PATH_QUERY)
#define ifPU if constexpr(HAS_PATH_UPDATE)
#define ifSQ if constexpr(HAS_SUBTREE_QUERY)
#define ifSU if constexpr(HAS_SUBTREE_UPDATE)
#define ifNC if constexpr(!IS_COMMUTATIVE)
#define ifPUSU if constexpr(HAS_PATH_UPDATE || HAS_SUBTREE_UPDATE)
	// If there is path update and subtree query, it needs path aggregation to do lazy propagation
	static_assert(HAS_PATH_QUERY || !HAS_PATH_UPDATE || !HAS_SUBTREE_QUERY);
	// If there is subtree query, T has to be commutative and invertible
	static_assert(!HAS_SUBTREE_QUERY || IS_COMMUTATIVE);
	vector<int> size, lazy_flip, pv, left, right;
	vector<T> data;
	vector<T> aux_data; // aggregation of data in the subtree in the auxiliary splay tree, aggregates in fixed order
	vector<T> virtual_data; // aggregation of subtr data of virtual childs
	vector<T> subtr_data; // aggregation of data in the subtree in the auxiliary splay tree along with their virtual data
	vector<U> aux_lazy; // update splay subtree
	vector<U> virtual_lazy; // update virtual childs
	vector<U> subtr_lazy; // update splay subtree along with their virtual childs
	F1 TT; // monoid operation (always adjacent)
	T T_id; // monoid identity
	F2 Tinv; // group inverse
	F3 Tflip; // flip the operation order
	F4 UU; // monoid operation (superset, subset)
	U U_id; // monoid identity
	F5 Uinv; // group inverse
	F6 UT; // action of U on T (superset, subset)
	link_cut_trees_base(F1 TT, T T_id, F2 Tinv, F3 Tflip, F4 UU, U U_id, F5 Uinv, F6 UT): TT(TT), T_id(T_id), Tinv(Tinv), Tflip(Tflip), UU(UU), U_id(U_id), Uinv(Uinv), UT(UT){ }
	void _apply_aux(int u, const U &f){
		static_assert(HAS_PATH_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		data[u] = UT(f, data[u]);
		aux_lazy[u] = UU(f, aux_lazy[u]);
		ifPQ{
			T x = UT(f, aux_data[u]);
			ifSQ subtr_data[u] = TT(x, TT(subtr_data[u], Tinv(aux_data[u])));
			aux_data[u] = x;
		}
	}
	void _apply_subtr(int u, const U &f){
		static_assert(HAS_SUBTREE_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		data[u] = UT(f, data[u]);
		ifPQ aux_data[u] = UT(f, aux_data[u]);
		ifSQ{
			virtual_data[u] = UT(f, virtual_data[u]);
			subtr_data[u] = UT(f, subtr_data[u]);
		}
		virtual_lazy[u] = UU(f, virtual_lazy[u]);
		subtr_lazy[u] = UU(f, subtr_lazy[u]);
	}
	void _apply_flip(int u){
		ASSERT(0 <= u && u < (int)data.size());
		lazy_flip[u] ^= 1;
		ifNC aux_data[u] = Tflip(aux_data[u]);
		swap(left[u], right[u]);
	}
	template<bool sign>
	void _apply_virtual(int u, int v){
		static_assert(HAS_SUBTREE_QUERY || HAS_SUBTREE_UPDATE);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if constexpr(sign == 0){
			ifSQ virtual_data[u] = TT(virtual_data[u], subtr_data[v]);
			ifSU _apply_subtr(v, Uinv(virtual_lazy[u]));
		}
		else{
			ifSU _apply_subtr(v, virtual_lazy[u]);
			ifSQ virtual_data[u] = TT(virtual_data[u], Tinv(subtr_data[v]));
		}
	}
	void _push(int u){
		ASSERT(0 <= u && u < (int)data.size());
		ifPU if(aux_lazy[u] != U_id){
			if(~left[u]) _apply_aux(left[u], aux_lazy[u]);
			if(~right[u]) _apply_aux(right[u], aux_lazy[u]);
			aux_lazy[u] = U_id;
		}
		ifSU{
			if(subtr_lazy[u] != U_id){
				if(~left[u]) _apply_subtr(left[u], subtr_lazy[u]);
				if(~right[u]) _apply_subtr(right[u], subtr_lazy[u]);
				subtr_lazy[u] = U_id;
			}
		}
		if(lazy_flip[u]){
			if(~left[u]) _apply_flip(left[u]);
			if(~right[u]) _apply_flip(right[u]);
			lazy_flip[u] = false;
		}
	}
	void _refresh(int u){
		ASSERT(0 <= u && u < (int)data.size());
		ifPU ASSERT(aux_lazy[u] == U_id);
		ifSU ASSERT(subtr_lazy[u] == U_id);
		size[u] = 1 + _internal_size(left[u]) + _internal_size(right[u]);
		ifPQ aux_data[u] = data[u];
		ifSQ subtr_data[u] = TT(data[u], virtual_data[u]);
		if(auto v = left[u]; ~v){
			ifPQ aux_data[u] = TT(aux_data[v], aux_data[u]);
			ifSQ subtr_data[u] = TT(subtr_data[u], subtr_data[v]);
		}
		if(auto w = right[u]; ~w){
			ifPQ aux_data[u] = TT(aux_data[u], aux_data[w]);
			ifSQ subtr_data[u] = TT(subtr_data[u], subtr_data[w]);
		}
	}
	int _dir(int u){
		ASSERT(0 <= u && u < (int)data.size());
		if(!~pv[u]) return -2; // root of its splay tree which contains LCT component root
		if(left[pv[u]] == u) return 0; // left child
		if(right[pv[u]] == u) return 1; // right child
		return -1; // root of its splay tree which does not contain LCT component root
	}
	bool _is_auxiliary_root(int u){
		ASSERT(0 <= u && u < (int)data.size());
		return _dir(u) < 0;
	}
	void _set_link(int u, int v, int d){
		ASSERT(-1 <= min(u, v) && max(u, v) < (int)data.size());
		if(~v) pv[v] = u;
		if(d >= 0) (d == 0 ? left : right)[u] = v;
	}
	// Assumes p and p->p propagated
	void _rotate(int u){
		ASSERT(0 <= u && u < (int)data.size() && !_is_auxiliary_root(u));
		int x = _dir(u), g = pv[u];
		_set_link(pv[g], u, _dir(g));
		_set_link(g, x == 1 ? left[u] : right[u], x);
		_set_link(u, g, x ^ 1);
		_refresh(g);
	}
	// Bring the node to the top
	void _splay(int u){
		ASSERT(0 <= u && u < (int)data.size());
		for(; !_is_auxiliary_root(u) && !_is_auxiliary_root(pv[u]); _rotate(u)){
			_push(pv[pv[u]]), _push(pv[u]), _push(u);
			_dir(u) == _dir(pv[u]) ? _rotate(pv[u]) : _rotate(u);
		}
		if(!_is_auxiliary_root(u)) _push(pv[u]), _push(u), _rotate(u);
		_push(u), _refresh(u);
	}
	int _internal_size(int u){
		ASSERT(-1 <= u && u < (int)data.size());
		return ~u ? size[u] : 0;
	}
	// Put u on the preferred path then splay it (right subtree is empty)
	void _access(int u){
		ASSERT(0 <= u && u < (int)data.size());
		for(auto v = u, p = -1; ~v; v = pv[p = v]){
			_splay(v);
			if constexpr(HAS_SUBTREE_QUERY || HAS_SUBTREE_UPDATE){
				if(~p) _apply_virtual<1>(v, p);
				if(~right[v]) _apply_virtual<0>(v, right[v]);
			}
			right[v] = p;
			_refresh(v);
		}
		_splay(u);
		ASSERT(!~right[u]);
	}
	void build(int n){
		ASSERT(0 <= n);
		build(vector<T>(n, T_id));
	}
	void build(int n, T init){
		ASSERT(0 <= n);
		build(vector<T>(n, init));
	}
	template<class V>
	void build(const vector<V> &a){
		int n = (int)a.size();
		size.assign(n, 1);
		lazy_flip.assign(n, false);
		pv.assign(n, -1);
		left.assign(n, -1);
		right.assign(n, -1);
		data = vector<T>(a.begin(), a.end());
		ifPQ aux_data = vector<T>(a.begin(), a.end());
		ifSQ{
			virtual_data.assign(n, T_id);
			subtr_data = data;
		}
		ifPU aux_lazy.assign(n, U_id);
		ifSU{
			virtual_lazy.assign(n, U_id);
			subtr_lazy.assign(n, U_id);
		}
	}
	int new_node(const T &x){
		size.push_back(1);
		lazy_flip.push_back(false);
		pv.push_back(-1);
		left.push_back(-1);
		right.push_back(-1);
		data.push_back(x);
		ifPQ aux_data.push_back(x);
		ifSQ{
			virtual_data.push_back(T_id);
			subtr_data.push_back(x);
		}
		ifPU aux_lazy.push_back(U_id);
		ifSU{
			virtual_lazy.push_back(U_id);
			subtr_lazy.push_back(U_id);
		}
		return (int)data.size() - 1;
	}
	// Make u the root of its connected component
	void reroot(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u), _apply_flip(u), _access(u);
		ASSERT(!~left[u] && !~right[u]);
	}
	int root_of(int u){
		ASSERT(0 <= u && u < (int)data.size());
		for(_access(u); ~left[u]; _push(u)) u = left[u];
		return _access(u), u;
	}
	// If u is a non-root vertex in its component, return its parent
	// Otherwise, return -1
	int parent_or_is_root(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		if(!~left[u]) return -1;
		for(_push(u = left[u]); ~right[u]; _push(u)) u = right[u];
		return _access(u), u;
	}
	// If u and v are in the same component, find the lca
	// Otherwise, return -1
	int lca_or_disconnected(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if(u == v) return u;
		_access(u), _access(v);
		if(!~pv[u]) return -1;
		_splay(u);
		return ~pv[u] ? pv[u] : u;
	}
	bool adjacent(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if(u == v) return false;
		int w = lca_or_disconnected(u, v);
		if(!~w || u != w && v != w) return false;
		return u != w ? w == parent_or_is_root(u) : w == parent_or_is_root(v);
	}
	int depth(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		return _internal_size(left[u]);
	}
	template<bool RESTORE_ROOT = true>
	int distance(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v);
		int res = _internal_size(left[v]);
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	bool connected(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size());
		if(u == v) return true;
		_access(u), _access(v);
		return ~pv[u];
	}
	// Returns the k-th ancestor on the path to root
	int find_ancestor_by_order(int u, int k){
		ASSERT(0 <= u && u < (int)data.size() && 0 <= k);
		k = depth(u) - k;
		ASSERT(k >= 0);
		for(; ; _push(u)){
			int size = _internal_size(left[u]);
			if(size == k) return _access(u), u;
			if(size < k) k -= size + 1, u = right[u];
			else u = left[u];
		}
		ASSERT(false);
	}
	// Returns the k-th vertex on the u-v path
	template<bool RESTORE_ROOT = true>
	int find_vertex_by_order(int u, int v, int k){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v) && 0 <= k);
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(v);
		int res = find_ancestor_by_order(u, k);
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	// Make u the parent of v
	void link(int u, int v){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && !connected(u, v));
		reroot(v), _access(u), _set_link(v, u, 0), _refresh(v);
	}
	void cut_from_parent(int u){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		ASSERT(~left[u]); // Assumes u is not the root of its component
		left[u] = pv[left[u]] = -1;
		_refresh(u);
	}
	// Assumes u and v are adjacent in tree
	void cut(int u, int v){
		ASSERT(adjacent(u, v));
		cut_from_parent(depth(u) > depth(v) ? u : v);
	}
	T query(int u){
		ASSERT(0 <= u && u < (int)data.size());
		ifPUSU _access(u);
		return data[u];
	}
	template<bool RESTORE_ROOT = true>
	T query_path(int u, int v){
		static_assert(HAS_PATH_QUERY);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v);
		T res = aux_data[v];
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	T query_subtree(int u){
		static_assert(HAS_SUBTREE_QUERY);
		ASSERT(0 <= u && u < (int)data.size());
		int v = parent_or_is_root(u);
		if(~v) cut_from_parent(u);
		T res = subtr_data[u];
		if(~v) link(v, u);
		return res;
	}
	void set(int u, const T &x){
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		data[u] = x;
		_refresh(u);
	}
	void update(int u, const U &f){
		static_assert(HAS_PATH_UPDATE || HAS_SUBTREE_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		_access(u);
		data[u] = UT(f, data[u]);
		_refresh(u);
	}
	template<bool RESTORE_ROOT = true>
	void update_path(int u, int v, const U &f){
		static_assert(HAS_PATH_UPDATE);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v), _apply_aux(v, f);
		if constexpr(RESTORE_ROOT) reroot(init_root);
	}
	void update_subtree(int u, const U &f){
		static_assert(HAS_SUBTREE_UPDATE);
		ASSERT(0 <= u && u < (int)data.size());
		int v = parent_or_is_root(u);
		if(~v) cut_from_parent(u);
		_apply_subtr(u, f);
		if(~v) link(v, u);
	}
	// Let the data on the u-v path be represented by an array A
	// A must be sorted by pred
	// Returns the r where everything in A[0, r) evaluates to true, and A[r, len(A)) evalutes to false
	template<bool RESTORE_ROOT = true>
	int partition_point(int u, int v, auto pred){
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u), _access(v);
		int res = 0;
		while(true){
			_push(v);
			if(pred(data[v])){
				res += _internal_size(left[v]) + 1;
				if(!~right[v]){
					_splay(v);
					break;
				}
				v = right[v];
			}
			else{
				if(!~left[v]){
					_splay(v);
					break;
				}
				v = left[v];
			}
		}
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
	// Let the data on the u-v path be represented by an array A
	// Assumes pred(A[0, r)) is T, ..., T, F, ..., F for 0 <= r <= len(A)
	// Returns max r with T
	template<bool RESTORE_ROOT = true>
	int max_pref(int u, int v, auto pred){
		static_assert(HAS_PATH_QUERY);
		ASSERT(0 <= min(u, v) && max(u, v) < (int)data.size() && connected(u, v) && pred(T_id));
		int init_root = -1;
		if constexpr(RESTORE_ROOT) init_root = root_of(u);
		reroot(u);
		int n = depth(v) + 1;
		if(pred(aux_data[v])){
			if constexpr(RESTORE_ROOT) reroot(init_root);
			return n;
		}
		T sum = T_id;
		auto recurse = [&](auto self, int u, int l)->int{
			if(!~u) return n;
			if(auto x = TT(sum, aux_data[u]); pred(x)){
				sum = x;
				return n;
			}
			_push(u);
			if(auto p = self(self, left[u], l); p < n) return p;
			l += _internal_size(left[u]);
			if(!pred(sum = TT(sum, data[u]))){
				_splay(u);
				return l;
			}
			return self(self, right[u], l + 1);
		};
		int res = recurse(recurse, v, 0);
		if constexpr(RESTORE_ROOT) reroot(init_root);
		return res;
	}
#undef ASSERT
#undef ifPQ
#undef ifPU
#undef ifSQ
#undef ifSU
#undef ifNC
#undef ifPUSU
};

template<class T>
auto make_LCT(){
	using U = int;
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<false, false, false, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class F1, class F3>
auto make_PQ_LCT(F1 TT, T T_id, F3 Tflip){
	using U = int;
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<true, false, false, false, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path update
template<class T, class U, class F4, class F6>
auto make_PU_LCT(F4 UU, U U_id, F6 UT){
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	return link_cut_trees_base<false, true, false, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - subtree query (commutative & invertible)
template<class T, class F1, class F2>
auto make_SQ_LCT(F1 TT, T T_id, F2 Tinv){
	using U = int;
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<false, false, true, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports:
// - subtree update (commutative & invertible)
template<class T, class U, class F4, class F5, class F6>
auto make_SU_LCT(F4 UU, U U_id, F5 Uinv, F6 UT){
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<false, false, false, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// - path update
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class U, class F1, class F3, class F4, class F6>
auto make_PQPU_LCT(F1 TT, T T_id, F3 Tflip, F4 UU, U U_id, F6 UT){
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	return link_cut_trees_base<true, true, false, false, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
template<class T, class F1, class F2>
auto make_PQSQ_LCT(F1 TT, T T_id, F2 Tinv){
	using U = int;
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto UU = [&](){ assert(false); };
	using F4 = decltype(UU);
	U U_id = {};
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	auto UT = [&](){ assert(false); };
	using F6 = decltype(UT);
	return link_cut_trees_base<true, false, true, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// - subtree update (commutative & invertible)
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class U, class F1, class F3, class F4, class F5, class F6>
auto make_PQSU_LCT(F1 TT, T T_id, F3 Tflip, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	return link_cut_trees_base<true, false, false, true, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree update (commutative & invertible)
template<class T, class U, class F4, class F5, class F6>
auto make_PUSU_LCT(F4 UU, U U_id, F5 Uinv, F6 UT){
	auto TT = [&](){ assert(false); };
	using F1 = decltype(TT);
	T T_id = {};
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<false, true, false, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - subtree query (commutative & invertible)
// - subtree update (commutative & invertible)
template<class T, class U, class F1, class F2, class F4, class F5, class F6>
auto make_SQSU_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<false, false, true, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
// - path update
template<class T, class U, class F1, class F2, class F4, class F6>
auto make_PQPUSQ_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	auto Uinv = [&](){ assert(false); };
	using F5 = decltype(Uinv);
	return link_cut_trees_base<true, true, true, false, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path query
// - path + subtree update (commutative & invertible)
// IS_COMMUTATIVE = true results in slightly better constant factor, Tflip is totally ignored in such case
template<bool IS_COMMUTATIVE, class T, class U, class F1, class F3, class F4, class F5, class F6>
auto make_PQPUSU_LCT(F1 TT, T T_id, F3 Tflip, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tinv = [&](){ assert(false); };
	using F2 = decltype(Tinv);
	return link_cut_trees_base<true, true, false, true, IS_COMMUTATIVE, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
// - subtree update (commutative & invertible)
template<class T, class U, class F1, class F2, class F4, class F5, class F6>
auto make_PQSQSU_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<true, false, true, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}
// Supports
// - path + subtree query (commutative & invertible)
// - path + subtree update (commutative & invertible)
template<class T, class U, class F1, class F2, class F4, class F5, class F6>
auto make_PQPUSQSU_LCT(F1 TT, T T_id, F2 Tinv, F4 UU, U U_id, F5 Uinv, F6 UT){
	auto Tflip = [&](){ assert(false); };
	using F3 = decltype(Tflip);
	return link_cut_trees_base<true, true, true, true, true, T, U, F1, F2, F3, F4, F5, F6>(TT, T_id, Tinv, Tflip, UU, U_id, Uinv, UT);
}

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n, qn;
	cin >> n >> qn;
	using T = pair<long long, int>;
	auto TT = [&](const T &x, const T &y)->T{
		return {
			x.first + y.first,
			x.second + y.second
		};
	};
	T T_id{};
	auto Tinv = [&](const T &x)->T{
		return {
			-x.first,
			-x.second
		};
	};
	auto UT = [&](long long f, const T &x)->T{
		return {x.first + x.second * f, x.second};
	};
	auto lct = make_PQPUSU_LCT<true>(TT, T_id, [&](){  }, plus<>(), 0LL, negate<>(), UT);
	vector<T> init(n, {0, 1});
	for(auto &x: init | ranges::views::keys){
		cin >> x;
	}
	lct.build(init);
	for(auto qi = 0; qi < qn; ++ qi){
		string op;
		cin >> op;
		if(op == "link"){
			int u, v;
			cin >> u >> v;
			lct.link(u, v);
		}
		else if(op == "cut"){
			int u, v;
			cin >> u >> v;
			lct.cut(u, v);
		}
		else if(op == "reroot"){
			int u;
			cin >> u;
			lct.reroot(u);
		}
		else if(op == "root_of"){
			int u;
			cin >> u;
			cout << lct.root_of(u) << "\n";
		}
		else if(op == "parent_or_is_root"){
			int u;
			cin >> u;
			cout << lct.parent_or_is_root(u) << '\n';
		}
		else if(op == "lca_or_disconnected"){
			int u, v;
			cin >> u >> v;
			cout << lct.lca_or_disconnected(u, v) << '\n';
		}
		else if(op == "adjacent"){
			int u, v;
			cin >> u >> v;
			cout << lct.adjacent(u, v) << "\n";
		}
		else if(op == "depth"){
			int u; cin >> u;
			cout << lct.depth(u) << '\n';
		}
		else if(op == "distance"){
			int u, v; cin >> u >> v;
			cout << lct.distance(u, v) << "\n";
		}
		else if(op == "connected"){
			int u, v; cin >> u >> v;
			cout << lct.connected(u, v) << "\n";
		}
		else if(op == "find_ancestor_by_order"){
			int u, k; cin >> u >> k;
			cout << lct.find_ancestor_by_order(u, k) << "\n";
		}
		else if(op == "find_vertex_by_order"){
			int u, v, k; cin >> u >> v >> k;
			cout << lct.find_vertex_by_order(u, v, k) << "\n";
		}
		else if(op == "query"){
			int u;
			cin >> u;
			cout << lct.query(u).first << "\n";
		}
		else if(op == "query_path"){
			int u, v;
			cin >> u >> v;
			cout << lct.query_path(u, v).first << "\n";
		}
		else if(op == "query_subtree"){
			// int u;
			// cin >> u;
			// cout << lct.query_subtree(u).first << "\n";
		}
		else if(op == "set"){
			int u, x;
			cin >> u >> x;
			lct.set(u, T{x, 1});
		}
		else if(op == "update"){
			int u, f;
			cin >> u >> f;
			lct.update(u, f);
		}
		else if(op == "update_path"){
			int u, v, f;
			cin >> u >> v >> f;
			lct.update_path(u, v, f);
		}
		else if(op == "update_subtree"){
			int u, f;
			cin >> u >> f;
			lct.update_subtree(u, f);
		}
		else if(op == "partition_point"){
			int u, v;
			long long x;
			cin >> u >> v >> x;
			cout << lct.partition_point(u, v, [&](auto data){ return data.first < x; }) << "\n";
		}
		else if(op == "max_pref"){
			int u, v;
			long long x;
			cin >> u >> v >> x;
			cout << lct.max_pref(u, v, [&](auto sum){ return sum.first < x; }) << "\n";
		}
		else{
			assert(false);
		}
		cout.flush();
	}
	return 0;
}

/*
debug(lct.size);
debug(lct.lazy_flip);
debug(lct.pv);
debug(lct.left);
debug(lct.right);
debug(lct.data);
debug(lct.aux_data);
debug(lct.virtual_data);
debug(lct.subtr_data);
debug(lct.aux_lazy);
debug(lct.virtual_lazy);
debug(lct.subtr_lazy);
debug_endl();
*/
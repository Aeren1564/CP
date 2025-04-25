// #pragma GCC optimize("O3,unroll-loops")
#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
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



int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n = rng() % 100 + 1, qn = 100, mx = rng() % 100 + 1;
	cout << n << " " << qn << "\n";
	for(auto i = 0; i < n; ++ i){
		cout << rng() % mx << " ";
	}
	cout << "\n\n";
	for(auto qi = 0; qi < qn; ++ qi){
		int type = rng() % 6, u = rng() % (qi + 1);
		if(type == 6 || type == 7){
			-- qi;
			continue;
		}
		cout << type << " " << u << "\n";
		if(type == 0){ // copy

		}
		else if(type == 1){ // point query_action
			cout << rng() % n << "\n";
		}
		else if(type == 2){ // to_array_action

		}
		else if(type == 3){ // point set_action
			cout << rng() % n << " " << rng() % mx << "\n";
		}
		else if(type == 4){ // point update
			cout << rng() % n << " " << rng() % mx << "\n";
		}
		else if(type == 5){ // range update
			auto [ql, qr] = gen_range(n);
			cout << ql << " " << qr << " " << rng() % mx << "\n";
		}
		else{
			assert(false);
		}
		cout << "\n";
	}
	return 0;
}

/*
0 int copy(int u)
	pair<int, T> query(int u, int p){	
		static_assert(HAS_QUERY);
1	pair<int, U> query_action(int u, int p){
		static_assert(!HAS_QUERY && HAS_UPDATE);
	pair<int, T> query(int u, int ql, int qr){
		static_assert(HAS_QUERY);
	pair<int, T> query_all(int u) const{
		static_assert(HAS_QUERY);
	pair<int, vector<T>> to_array(int u){
		static_assert(HAS_QUERY);
2	pair<int, vector<U>> to_array_of_updates(int u){
		static_assert(!HAS_QUERY && HAS_UPDATE);
	int set(int u, int p, T x){
		static_assert(HAS_QUERY);
3	int set_action(int u, int p, U f){
		static_assert(!HAS_QUERY && HAS_UPDATE);
4	int update(int u, int p, U f){
		static_assert(HAS_UPDATE);
5	int update(int u, int ql, int qr, U f){
		static_assert(HAS_UPDATE);
	pair<int, int> max_pref(int u, int ql, auto pred){
		static_assert(HAS_QUERY);
	pair<int, int> min_suff(int u, int qr, auto pred){
		static_assert(HAS_QUERY);
*/
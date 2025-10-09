// #pragma GCC optimize("O3,unroll-loops")
#include <bits/stdc++.h>
// #include <x86intrin.h>
using namespace std;
#if __cplusplus >= 202002L
using namespace numbers;
#endif



int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n, qn;
	cin >> n >> qn;
	vector<vector<long long>> a(qn + 1, vector<long long>(n));
	copy_n(istream_iterator<long long>(cin), n, a[0].begin());
	for(auto qi = 0; qi < qn; ++ qi){
		int type, u;
		cin >> type >> u;
		auto &cur = a[qi + 1];
		cur = a[u];
		if(type == 0){ // copy

		}
		else if(type == 1){ // point query_action
			int p;
			cin >> p;
			cout << cur[p] << "\n";
		}
		else if(type == 2){ // to_array_action
			for(auto i = 0; i < n; ++ i){
				cout << cur[i] << " ";
			}
			cout << "\n";
		}
		else if(type == 3){ // point set_action
			int p, x;
			cin >> p >> x;
			cur[p] = x;
		}
		else if(type == 4){ // point update
			int p, f;
			cin >> p >> f;
			cur[p] += f;
		}
		else if(type == 5){ // range update
			int ql, qr, f;
			cin >> ql >> qr >> f;
			for(auto i = ql; i < qr; ++ i){
				cur[i] += f;
			}
		}
		else{
			assert(false);
		}
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
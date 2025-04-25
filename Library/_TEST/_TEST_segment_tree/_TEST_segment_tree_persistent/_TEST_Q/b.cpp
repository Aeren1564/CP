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
		else if(type == 1){ // point query
			int p;
			cin >> p;
			cout << cur[p] << "\n";
		}
		else if(type == 2){ // range query
			int ql, qr;
			cin >> ql >> qr;
			cout << accumulate(cur.begin() + ql, cur.begin() + qr, 0LL, [&](auto x, auto y){ return max(x, y); }) << "\n";
		}
		else if(type == 3){ // all query
			cout << accumulate(cur.begin(), cur.end(), 0LL, [&](auto x, auto y){ return max(x, y); }) << "\n";
		}
		else if(type == 4){ // to_array
			for(auto i = 0; i < n; ++ i){
				cout << cur[i] << " ";
			}
			cout << "\n";
		}
		else if(type == 5){ // point set
			int p, x;
			cin >> p >> x;
			cur[p] = x;
		}
		else if(type == 6){ // point update
			int p, f;
			cin >> p >> f;
			cur[p] += f;
		}
		else if(type == 7){ // range update
			int ql, qr, f;
			cin >> ql >> qr >> f;
			for(auto i = ql; i < qr; ++ i){
				cur[i] += f;
			}
		}
		else if(type == 8){ // max pref
			int ql;
			long long th;
			cin >> ql >> th;
			int r = ql;
			while(r < n && cur[r] <= th){
				++ r;
			}
			cout << r << "\n";
		}
		else if(type == 9){ // min suff
			int qr;
			long long th;
			cin >> qr >> th;
			int l = qr;
			while(l > 0 && cur[l - 1] <= th){
				-- l;
			}
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
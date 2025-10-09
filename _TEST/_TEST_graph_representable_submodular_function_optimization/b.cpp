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
	int nv, minimize, n;
	cin >> nv >> minimize >> n;
	int c = 0;
	vector<tuple<int, array<int, 2>>> linear;
	vector<tuple<int, int, array<array<int, 2>, 2>>> quad;
	vector<tuple<int, int, int, array<array<array<int, 2>, 2>, 2>>> cubic;
	vector<tuple<vector<int>, bool, int>> restricted;
	for(auto i = 0; i < n; ++ i){
		int type;
		cin >> type;
		if(type == 0){
			int x;
			cin >> x;
			c += x;
		}
		else if(type == 1){
			int i;
			array<int, 2> x;
			cin >> i >> x[0] >> x[1];
			linear.push_back({i, x});
		}
		else if(type == 2){
			int i, j;
			array<array<int, 2>, 2> x;
			cin >> i >> j;
			for(auto p = 0; p < 2; ++ p){
				for(auto q = 0; q < 2; ++ q){
					cin >> x[p][q];
				}
			}
			quad.push_back({i, j, x});
		}
		else if(type == 3){
			int i, j, k;
			array<array<array<int, 2>, 2>, 2> x;
			cin >> i >> j >> k;
			for(auto p = 0; p < 2; ++ p){
				for(auto q = 0; q < 2; ++ q){
					for(auto r = 0; r < 2; ++ r){
						cin >> x[p][q][r];
					}
				}
			}
			cubic.push_back({i, j, k, x});
		}
		else{
			int m, base, value;
			cin >> m >> base >> value;
			vector<int> a(m);
			for(auto i = 0; i < m; ++ i){
				cin >> a[i];
			}
			restricted.push_back({a, base, value});
		}
	}
	int value;
	vector<int> assignment(nv);
	cin >> value;
	{
		string s;
		cin >> s;
		for(auto i = 0; i < nv; ++ i){
			assignment[i] = s[i] - '0';
		}
	}
	auto eval = [&](vector<int> assignment)->int{
		int res = c;
		for(auto [i, x]: linear){
			res += x[assignment[i]];
		}
		for(auto [i, j, x]: quad){
			res += x[assignment[i]][assignment[j]];
		}
		for(auto [i, j, k, x]: cubic){
			res += x[assignment[i]][assignment[j]][assignment[k]];
		}
		for(auto [a, base, value]: restricted){
			for(auto i: a){
				if(assignment[i] != base){
					goto NEXT;
				}
			}
			res += value;
			NEXT:;
		}
		return res;
	};
	int opt = minimize ? numeric_limits<int>::max() : numeric_limits<int>::min();
	for(auto mask = 0; mask < 1 << nv; ++ mask){
		vector<int> assignment(nv);
		for(auto i = 0; i < nv; ++ i){
			assignment[i] = mask >> i & 1;
		}
		int cur = eval(assignment);
		if(minimize && opt > cur || !minimize && opt < cur){
			opt = cur;
		}
	}
	assert(opt == value);
	assert(eval(assignment) == value);
	return 0;
}

/*

*/
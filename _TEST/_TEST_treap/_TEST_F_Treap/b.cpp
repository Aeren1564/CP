#include <x86intrin.h>
#include <bits/stdc++.h>
using namespace std;
#if __cplusplus > 201703L
#include <ranges>
using namespace numbers;
#endif



int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int qn;
	cin >> qn;
	vector<int> a;
	for(auto qi = 0; qi < qn; ++ qi){
		int type;
		cin >> type;
		if(type == 0){ // insert
			int p, x;
			cin >> p >> x;
			assert(0 <= p && p <= (int)a.size());
			a.insert(a.begin() + p, x);
		}
		else if(type == 1){ // erase
			int p;
			cin >> p;
			assert(0 <= p && p < (int)a.size());
			a.erase(a.begin() + p);
		}
		else if(type == 2){ // flip
			int l, r;
			cin >> l >> r;
			assert(0 <= l && l <= r && r <= (int)a.size());
			reverse(a.begin() + l, a.begin() + r);
		}
		else if(type == 3){ // split
			int l, r;
			cin >> l >> r;
			assert(0 <= l && l <= r && r <= (int)a.size());
			a = vector<int>(a.begin() + l, a.begin() + r);
		}
		else{ // query
			int p;
			cin >> p;
			assert(0 <= p && p < (int)a.size());
			cout << a[p] << "\n";
		}
	}
	return 0;
}

/*

*/

////////////////////////////////////////////////////////////////////////////////////////
//                                                                                    //
//                                   Coded by Aeren                                   //
//                                                                                    //
////////////////////////////////////////////////////////////////////////////////////////
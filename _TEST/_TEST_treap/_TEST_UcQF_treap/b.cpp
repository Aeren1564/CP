#include <x86intrin.h>
#include <bits/stdc++.h>
using namespace std;
#if __cplusplus > 201703L
#include <ranges>
using namespace numbers;
#endif

using uint = unsigned int;
template<uint _mod>
struct modular_fixed_base{
	static constexpr uint mod(){
		return _mod;
	}
	template<class T>
	static vector<modular_fixed_base> precalc_power(T base, int SZ){
		vector<modular_fixed_base> res(SZ + 1, 1);
		for(auto i = 1; i <= SZ; ++ i) res[i] = res[i - 1] * base;
		return res;
	}
	static vector<modular_fixed_base> _INV;
	static void precalc_inverse(int SZ){
		if(_INV.empty()) _INV.assign(2, 1);
		for(auto x = _INV.size(); x <= SZ; ++ x) _INV.push_back(_mod / x * -_INV[_mod % x]);
	}
	// _mod must be a prime
	static modular_fixed_base _primitive_root;
	static modular_fixed_base primitive_root(){
		if(_primitive_root) return _primitive_root;
		if(_mod == 2) return _primitive_root = 1;
		if(_mod == 998244353) return _primitive_root = 3;
		uint divs[20] = {};
		divs[0] = 2;
		int cnt = 1;
		uint x = (_mod - 1) / 2;
		while(x % 2 == 0) x /= 2;
		for(auto i = 3; 1LL * i * i <= x; i += 2){
			if(x % i == 0){
				divs[cnt ++] = i;
				while(x % i == 0) x /= i;
			}
		}
		if(x > 1) divs[cnt ++] = x;
		for(auto g = 2; ; ++ g){
			bool ok = true;
			for(auto i = 0; i < cnt; ++ i){
				if((modular_fixed_base(g).power((_mod - 1) / divs[i])) == 1){
					ok = false;
					break;
				}
			}
			if(ok) return _primitive_root = g;
		}
	}
	constexpr modular_fixed_base(): data(){ }
	modular_fixed_base(const double &x){ data = normalize(llround(x)); }
	modular_fixed_base(const long double &x){ data = normalize(llround(x)); }
	template<class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base(const T &x){ data = normalize(x); }
	template<class T, typename enable_if<is_integral<T>::value>::type* = nullptr> static uint normalize(const T &x){
		int sign = x >= 0 ? 1 : -1;
		uint v =  _mod <= sign * x ? sign * x % _mod : sign * x;
		if(sign == -1 && v) v = _mod - v;
		return v;
	}
	const uint &operator()() const{ return data; }
	template<class T> operator T() const{ return data; }
	modular_fixed_base &operator+=(const modular_fixed_base &otr){ if((data += otr.data) >= _mod) data -= _mod; return *this; }
	modular_fixed_base &operator-=(const modular_fixed_base &otr){ if((data += _mod - otr.data) >= _mod) data -= _mod; return *this; }
	template<class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base &operator+=(const T &otr){ return *this += modular_fixed_base(otr); }
	template<class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base &operator-=(const T &otr){ return *this -= modular_fixed_base(otr); }
	modular_fixed_base &operator++(){ return *this += 1; }
	modular_fixed_base &operator--(){ return *this += _mod - 1; }
	modular_fixed_base operator++(int){ modular_fixed_base result(*this); *this += 1; return result; }
	modular_fixed_base operator--(int){ modular_fixed_base result(*this); *this += _mod - 1; return result; }
	modular_fixed_base operator-() const{ return modular_fixed_base(_mod - data); }
	modular_fixed_base &operator*=(const modular_fixed_base &rhs){
		data = (unsigned long long)data * rhs.data % _mod;
		return *this;
	}
	template<class T, typename enable_if<is_integral<T>::value>::type* = nullptr>
	modular_fixed_base &inplace_power(T e){
		if(e < 0) *this = 1 / *this, e = -e;
		modular_fixed_base res = 1;
		for(; e; *this *= *this, e >>= 1) if(e & 1) res *= *this;
		return *this = res;
	}
	template<class T, typename enable_if<is_integral<T>::value>::type* = nullptr>
	modular_fixed_base power(T e) const{
		return modular_fixed_base(*this).inplace_power(e);
	}
	modular_fixed_base &operator/=(const modular_fixed_base &otr){
		int a = otr.data, m = _mod, u = 0, v = 1;
		if(a < _INV.size()) return *this *= _INV[a];
		while(a){
			int t = m / a;
			m -= t * a; swap(a, m);
			u -= t * v; swap(u, v);
		}
		assert(m == 1);
		return *this *= u;
	}
	uint data;
};
template<uint _mod> vector<modular_fixed_base<_mod>> modular_fixed_base<_mod>::_INV;
template<uint _mod> modular_fixed_base<_mod> modular_fixed_base<_mod>::_primitive_root;
template<uint _mod> bool operator==(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return lhs.data == rhs.data; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> bool operator==(const modular_fixed_base<_mod> &lhs, T rhs){ return lhs == modular_fixed_base<_mod>(rhs); }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> bool operator==(T lhs, const modular_fixed_base<_mod> &rhs){ return modular_fixed_base<_mod>(lhs) == rhs; }
template<uint _mod> bool operator!=(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return !(lhs == rhs); }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> bool operator!=(const modular_fixed_base<_mod> &lhs, T rhs){ return !(lhs == rhs); }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> bool operator!=(T lhs, const modular_fixed_base<_mod> &rhs){ return !(lhs == rhs); }
template<uint _mod> bool operator<(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return lhs.data < rhs.data; }
template<uint _mod> bool operator>(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return lhs.data > rhs.data; }
template<uint _mod> bool operator<=(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return lhs.data <= rhs.data; }
template<uint _mod> bool operator>=(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return lhs.data >= rhs.data; }
template<uint _mod> modular_fixed_base<_mod> operator+(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return modular_fixed_base<_mod>(lhs) += rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator+(const modular_fixed_base<_mod> &lhs, T rhs){ return modular_fixed_base<_mod>(lhs) += rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator+(T lhs, const modular_fixed_base<_mod> &rhs){ return modular_fixed_base<_mod>(lhs) += rhs; }
template<uint _mod> modular_fixed_base<_mod> operator-(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return modular_fixed_base<_mod>(lhs) -= rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator-(const modular_fixed_base<_mod> &lhs, T rhs){ return modular_fixed_base<_mod>(lhs) -= rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator-(T lhs, const modular_fixed_base<_mod> &rhs){ return modular_fixed_base<_mod>(lhs) -= rhs; }
template<uint _mod> modular_fixed_base<_mod> operator*(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs){ return modular_fixed_base<_mod>(lhs) *= rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator*(const modular_fixed_base<_mod> &lhs, T rhs){ return modular_fixed_base<_mod>(lhs) *= rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator*(T lhs, const modular_fixed_base<_mod> &rhs){ return modular_fixed_base<_mod>(lhs) *= rhs; }
template<uint _mod> modular_fixed_base<_mod> operator/(const modular_fixed_base<_mod> &lhs, const modular_fixed_base<_mod> &rhs) { return modular_fixed_base<_mod>(lhs) /= rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator/(const modular_fixed_base<_mod> &lhs, T rhs) { return modular_fixed_base<_mod>(lhs) /= rhs; }
template<uint _mod, class T, typename enable_if<is_integral<T>::value>::type* = nullptr> modular_fixed_base<_mod> operator/(T lhs, const modular_fixed_base<_mod> &rhs) { return modular_fixed_base<_mod>(lhs) /= rhs; }
template<uint _mod> istream &operator>>(istream &in, modular_fixed_base<_mod> &number){
	long long x;
	in >> x;
	number.data = modular_fixed_base<_mod>::normalize(x);
	return in;
}
// #define _PRINT_AS_FRACTION
template<uint _mod> ostream &operator<<(ostream &out, const modular_fixed_base<_mod> &number){
#ifdef LOCAL
#ifdef _PRINT_AS_FRACTION
	out << number();
	cerr << "(";
	for(auto d = 1; ; ++ d){
		if((number * d).data <= 1000000){
			cerr << (number * d).data << "/" << d;
			break;
		}
		else if((-number * d).data <= 1000000){
			cerr << "-" << (-number * d).data << "/" << d;
			break;
		}
	}
	cerr << ")";
	return out;
#else
	return out << number();
#endif
#else
	return out << number();
#endif
}
#undef _PRINT_AS_FRACTION

// const uint mod = 1e9 + 7; // 1000000007
const uint mod = (119 << 23) + 1; // 998244353
// const uint mod = 1e9 + 9; // 1000000009
using modular = modular_fixed_base<mod>;

// T must support +=, -=, *, *=, ==, and !=
template<class T, size_t N, size_t M>
struct matrix_fixed{
	using ring_t = T;
	using domain_t = array<T, M>;
	using range_t = array<T, N>;
	int n, m;
	array<array<T, M>, N> data;
	array<T, M> &operator()(int i){
		assert(0 <= i && i < n);
		return data[i];
	}
	const array<T, M> &operator()(int i) const{
		assert(0 <= i && i < n);
		return data[i];
	}
	T &operator()(int i, int j){
		assert(0 <= i && i < n && 0 <= j && j < m);
		return data[i][j];
	}
	const T &operator()(int i, int j) const{
		assert(0 <= i && i < n && 0 <= j && j < m);
		return data[i][j];
	}
	bool operator==(const matrix_fixed &a) const{
		assert(n == a.n && m == a.m);
		return data == a.data;
	}
	bool operator!=(const matrix_fixed &a) const{
		assert(n == a.n && m == a.m);
		return data != a.data;
	}
	matrix_fixed &operator+=(const matrix_fixed &a){
		assert(n == a.n && m == a.m);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] += a(i, j);
		return *this;
	}
	matrix_fixed operator+(const matrix_fixed &a) const{
		assert(n == a.n && m == a.m);
		return matrix_fixed(*this) += a;
	}
	matrix_fixed &operator-=(const matrix_fixed &a){
		assert(n == a.n && m == a.m);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] += a(i, j);
		return *this;
	}
	matrix_fixed operator-(const matrix_fixed &a) const{
		assert(n == a.n && m == a.m);
		return matrix_fixed(*this) += a;
	}
	template<size_t N2, size_t M2>
	matrix_fixed<T, N, M2> operator*(const matrix_fixed<T, N2, M2> &a) const{
		assert(m == a.n);
		int l = M2;
		matrix_fixed<T, N, M2> res(n, a.m);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) for(auto k = 0; k < l; ++ k) res(i, k) += data[i][j] * a(j, k);
		return res;
	}
	template<size_t N2, size_t M2>
	matrix_fixed &operator*=(const matrix_fixed<T, N2, M2> &a){
		return *this = *this * a;
	}
	matrix_fixed &operator*=(T c){
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] *= c;
		return *this;
	}
	matrix_fixed operator*(T c) const{
		matrix_fixed res(data, n, m);
		return res *= c;
	}
	template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>
	matrix_fixed &inplace_power(U e){
		assert(n == m && e >= 0);
		matrix_fixed res(n, n, T(1));
		for(; e; *this *= *this, e >>= 1) if(e & 1) res *= *this;
		return *this = res;
	}
	template<class U>
	matrix_fixed power(U e) const{
		return matrix_fixed(*this).inplace_power(e);
	}
	matrix_fixed<T, M, N> transposed() const{
		matrix_fixed<T, M, N> res;
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) res(j, i) = data[i][j];
		return res;
	}
	matrix_fixed &transpose(){
		return *this = transposed();
	}
	// Multiply a column vector v on the right
	range_t operator*(const domain_t &v) const{
		range_t res;
		res.fill(T(0));
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) res[i] += data[i][j] * v[j];
		return res;
	}
	// Assumes T is a field
	// find_inverse() must return optional<T>
	// O(n) find_inverse() calls along with O(n^3) operations on T
	T determinant(auto find_inverse) const{
		assert(n == m);
		if(n == 0) return T(1);
		auto a = data;
		T res = T(1);
		for(auto j = 0; j < n; ++ j){
			int pivot = -1;
			for(auto i = j; i < n; ++ i) if(a[i][j] != T(0)){
				pivot = i;
				break;
			}
			if(!~pivot) return T(0);
			swap(a[j], a[pivot]);
			res *= a[j][j] * (j != pivot ? -1 : 1);
			auto invp = find_inverse(a[j][j]);
			assert(invp);
			T inv = *invp;
			for(auto i = j + 1; i < n; ++ i) if(i != j && a[i][j] != T(0)){
				T d = a[i][j] * inv;
				for(auto jj = j; jj < n; ++ jj) a[i][jj] -= d * a[j][jj];
			}
		}
		return res;
	}
	// Assumes T is a field
	// find_inverse() must return optional<T>
	// O(n) find_inverse() calls along with O(n^3) operations on T
	optional<matrix_fixed> inverse(auto find_inverse) const{
		assert(n == m);
		if(n == 0) return *this;
		auto a = data;
		array<array<T, M>, N> res;
		for(auto i = 0; i < n; ++ i) res[i].fill(T(0)), res[i][i] = T(1);
		for(auto j = 0; j < n; ++ j){
			int pivot = -1;
			for(auto i = j; i < n; ++ i) if(a[i][j] != T(0)){
				pivot = i;
				break;
			}
			if(!~pivot) return {};
			swap(a[j], a[pivot]), swap(res[j], res[pivot]);
			auto invp = find_inverse(a[j][j]);
			assert(invp);
			T inv = *invp;
			for(auto jj = 0; jj < n; ++ jj) a[j][jj] *= inv, res[j][jj] *= inv;
			for(auto i = 0; i < n; ++ i) if(i != j && a[i][j] != T(0)){
				T d = a[i][j];
				for(auto jj = 0; jj < n; ++ jj) a[i][jj] -= d * a[j][jj], res[i][jj] -= d * res[j][jj];
			}
		}
		return res;
	}
	template<class output_stream>
	friend output_stream &operator<<(output_stream &out, const matrix_fixed &a){
		out << "\n";
		for(auto i = 0; i < a.n; ++ i){
			for(auto j = 0; j < a.m; ++ j){
				out << a(i, j) << " ";
			}
			out << "\n";
		}
		return out;
	}
	matrix_fixed(int n, int m, T init_diagonal = T(0), T init_off_diagonal = T(0)): n(n), m(m){
		assert(0 <= min(n, m) && n <= N && m <= M);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] = i == j ? init_diagonal : init_off_diagonal;
	}
	matrix_fixed(const array<array<T, M>, N> &arr): n(N), m(M), data(arr){ }
};
template<class T, size_t N, size_t M>
matrix_fixed<T, N, M> operator*(T c, matrix_fixed<T, N, M> a){
	for(auto i = 0; i < a.n; ++ i) for(auto j = 0; j < a.m; ++ j) a(i, j) = c * a(i, j);
	return a;
}
// Multiply a row vector v on the left
template<class T, size_t N, size_t M>
matrix_fixed<T, N, M>::domain_t operator*(const typename matrix_fixed<T, N, M>::range_t &v, const matrix_fixed<T, N, M> &a){
	typename matrix_fixed<T, N, M>::domain_t res;
	res.fill(T(0));
	for(auto i = 0; i < a.n; ++ i) for(auto j = 0; j < a.m; ++ j) res[j] += v[i] * a(i, j);
	return res;
}

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int qn;
	cin >> qn;
	vector<long long> a;
	for(auto qi = 0; qi < qn; ++ qi){
		int type;
		cin >> type;
		if(type == 0){ // insert
			int p, x;
			cin >> p >> x;
			a.insert(a.begin() + p, x);
		}
		else if(type == 1){ // erase
			int p;
			cin >> p;
			a.erase(a.begin() + p);
		}
		else if(type == 2){ // set
			int p, x;
			cin >> p >> x;
			a[p] = x;
		}
		else if(type == 3){ // point update
			int p, f;
			cin >> p >> f;
			a[p] += f;
		}
		else if(type == 4){ // range update
			int l, r, f;
			cin >> l >> r >> f;
			assert(0 <= l && l <= r && r <= (int)a.size());
			for(auto i = l; i < r; ++ i){
				a[i] += f;
			}
		}
		else if(type == 5){ // point query
			int p;
			cin >> p;
			cout << a[p] << "\n";
		}
		else if(type == 6){ // range query
			int l, r;
			cin >> l >> r;
			assert(0 <= l && l <= r && r <= (int)a.size());
			long long res = 0;
			for(auto i = l; i < r; ++ i){
				res = max(res, a[i]);
			}
			cout << res << "\n";
		}
		else{ // range flip
			int l, r;
			cin >> l >> r;
			assert(0 <= l && l <= r && r <= (int)a.size());
			ranges::reverse(a.begin() + l, a.begin() + r);
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
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

template<class data_t, data_t _mod>
struct modular_fixed_base{
#define IS_INTEGRAL(T) (is_integral_v<T> || is_same_v<T, __int128_t> || is_same_v<T, __uint128_t>)
#define IS_UNSIGNED(T) (is_unsigned_v<T> || is_same_v<T, __uint128_t>)
	static_assert(IS_UNSIGNED(data_t));
	static_assert(1 <= _mod && _mod < data_t(1) << 8 * sizeof(data_t) - 1);
	static constexpr bool VARIATE_MOD_FLAG = false;
	static constexpr data_t mod(){
		return _mod;
	}
	template<class T>
	static constexpr vector<modular_fixed_base> precalc_power(T base, int SZ){
		vector<modular_fixed_base> res(SZ + 1, 1);
		for(auto i = 1; i <= SZ; ++ i) res[i] = res[i - 1] * base;
		return res;
	}
	template<class T>
	static constexpr vector<modular_fixed_base> precalc_geometric_sum(T base, int SZ){
		vector<modular_fixed_base> res(SZ + 1);
		for(auto i = 1; i <= SZ; ++ i) res[i] = res[i - 1] * base + base;
		return res;
	}
	static vector<modular_fixed_base> _INV;
	static constexpr void precalc_inverse(int SZ){
		if(_INV.empty()) _INV.assign(2, 1);
		for(auto x = _INV.size(); x <= SZ; ++ x) _INV.push_back(_mod / x * -_INV[_mod % x]);
	}
	// _mod must be a prime
	static modular_fixed_base _primitive_root;
	static constexpr modular_fixed_base primitive_root(){
		if(_primitive_root) return _primitive_root;
		if(_mod == 2) return _primitive_root = 1;
		if(_mod == 998244353) return _primitive_root = 3;
		data_t divs[20] = {};
		divs[0] = 2;
		int cnt = 1;
		data_t x = (_mod - 1) / 2;
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
				if(modular_fixed_base(g).power((_mod - 1) / divs[i]) == 1){
					ok = false;
					break;
				}
			}
			if(ok) return _primitive_root = g;
		}
	}
	constexpr modular_fixed_base(){ }
	constexpr modular_fixed_base(const double &x){ _data = _normalize(llround(x)); }
	constexpr modular_fixed_base(const long double &x){ _data = _normalize(llround(x)); }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr modular_fixed_base(const T &x){ _data = _normalize(x); }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> static constexpr data_t _normalize(const T &x){
		int sign = x >= 0 ? 1 : -1;
		data_t v =  _mod <= sign * x ? sign * x % _mod : sign * x;
		if(sign == -1 && v) v = _mod - v;
		return v;
	}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr operator T() const{ return data(); }
	constexpr modular_fixed_base &operator+=(const modular_fixed_base &otr){ if((_data += otr._data) >= _mod) _data -= _mod; return *this; }
	constexpr modular_fixed_base &operator-=(const modular_fixed_base &otr){ if((_data += _mod - otr._data) >= _mod) _data -= _mod; return *this; }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr modular_fixed_base &operator+=(const T &otr){ return *this += modular_fixed_base(otr); }
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr> constexpr modular_fixed_base &operator-=(const T &otr){ return *this -= modular_fixed_base(otr); }
	constexpr modular_fixed_base &operator++(){ return *this += 1; }
	constexpr modular_fixed_base &operator--(){ return *this += _mod - 1; }
	constexpr modular_fixed_base operator++(int){ modular_fixed_base result(*this); *this += 1; return result; }
	constexpr modular_fixed_base operator--(int){ modular_fixed_base result(*this); *this += _mod - 1; return result; }
	constexpr modular_fixed_base operator-() const{ return modular_fixed_base(_mod - _data); }
	constexpr modular_fixed_base &operator*=(const modular_fixed_base &rhs){
		if constexpr(is_same_v<data_t, unsigned int>) _data = (unsigned long long)_data * rhs._data % _mod;
		else if constexpr(is_same_v<data_t, unsigned long long>){
			long long res = _data * rhs._data - _mod * (unsigned long long)(1.L / _mod * _data * rhs._data);
			_data = res + _mod * (res < 0) - _mod * (res >= (long long)_mod);
		}
		else _data = _normalize(_data * rhs._data);
		return *this;
	}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base &inplace_power(T e){
		if(e == 0) return *this = 1;
		if(_data == 0) return *this = {};
		if(_data == 1 || e == 1) return *this;
		if(_data == mod() - 1) return e % 2 ? *this : *this = -*this;
		if(e < 0) *this = 1 / *this, e = -e;
		if(e == 1) return *this;
		modular_fixed_base res = 1;
		for(; e; *this *= *this, e >>= 1) if(e & 1) res *= *this;
		return *this = res;
	}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base power(T e) const{
		return modular_fixed_base(*this).inplace_power(e);
	}
	// c + c * x + ... + c * x^{e-1}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base &inplace_geometric_sum(T e, modular_fixed_base c = 1){
		if(e == 0) return *this = {};
		if(_data == 0) return *this = {};
		if(_data == 1) return *this = c * e;
		if(e == 1) return *this = c;
		if(_data == mod() - 1) return *this = c * abs(e % 2);
		modular_fixed_base res = 0;
		if(e < 0) return *this = geometric_sum(-e + 1, -*this) - 1;
		if(e == 1) return *this = c * *this;
		for(; e; c *= 1 + *this, *this *= *this, e >>= 1) if(e & 1) res += c, c *= *this;
		return *this = res;
	}
	// c + c * x + ... + c * x^{e-1}
	template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>
	constexpr modular_fixed_base geometric_sum(T e, modular_fixed_base c = 1) const{
		return modular_fixed_base(*this).inplace_geometric_sum(e, c);
	}
	// Returns the minimum integer e>0 with b^e=*this, if it exists
	// O(sqrt(mod)) applications of hashmap
	constexpr optional<data_t> log(const modular_fixed_base &b) const{
		data_t m = mod(), n = sqrtl(m) + 1, j = 1;
		modular_fixed_base e = 1, f = 1;
		unordered_map<data_t, data_t> A;
		while(j <= n && (f = e *= b) != *this) A[(e * *this).data()] = j ++;
		if(e == *this) return j;
		if(gcd(mod(), e.data()) == gcd(mod(), data())) for(auto i = 2; i < n + 2; ++ i) if(A.count((e *= f).data())) return n * i - A[e.data()];
		return {};
	}
	constexpr optional<modular_fixed_base> inverse() const{
		make_signed_t<data_t> a = data(), m = _mod, u = 0, v = 1;
		if(data() < _INV.size()) return _INV[data()];
		while(a){
			make_signed_t<data_t> t = m / a;
			m -= t * a; swap(a, m);
			u -= t * v; swap(u, v);
		}
		if(m != 1) return {};
		return modular_fixed_base{u};
	}
	modular_fixed_base &operator/=(const modular_fixed_base &otr){
		auto inv_ptr = otr.inverse();
		assert(inv_ptr);
		return *this = *this * *inv_ptr;
	}
#define ARITHMETIC_OP(op, apply_op)\
constexpr modular_fixed_base operator op(const modular_fixed_base &x) const{ return modular_fixed_base(*this) apply_op x; }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr modular_fixed_base operator op(const T &x) const{ return modular_fixed_base(*this) apply_op modular_fixed_base(x); }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr friend modular_fixed_base operator op(const T &x, const modular_fixed_base &y){ return modular_fixed_base(x) apply_op y; }
	ARITHMETIC_OP(+, +=) ARITHMETIC_OP(-, -=) ARITHMETIC_OP(*, *=) ARITHMETIC_OP(/, /=)
#undef ARITHMETIC_OP
#define COMPARE_OP(op)\
constexpr bool operator op(const modular_fixed_base &x) const{ return _data op x._data; }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr bool operator op(const T &x) const{ return _data op modular_fixed_base(x)._data; }\
template<class T, typename enable_if<IS_INTEGRAL(T)>::type* = nullptr>\
constexpr friend bool operator op(const T &x, const modular_fixed_base &y){ return modular_fixed_base(x)._data op y._data; }
	COMPARE_OP(==) COMPARE_OP(!=) COMPARE_OP(<) COMPARE_OP(<=) COMPARE_OP(>) COMPARE_OP(>=)
#undef COMPARE_OP
	friend istream &operator>>(istream &in, modular_fixed_base &number){
		long long x;
		in >> x;
		number._data = modular_fixed_base::_normalize(x);
		return in;
	}
	friend ostream &operator<<(ostream &out, const modular_fixed_base &number){
		out << number._data;
#ifdef LOCAL
		cerr << "(";
		for(auto d = 1; ; ++ d){
			if((number * d)._data <= 1000000){
				cerr << (number * d)._data;
				if(d != 1) cerr << "/" << d;
				break;
			}
			else if((-number * d)._data <= 1000000){
				cerr << "-" << (-number * d)._data;
				if(d != 1) cerr << "/" << d;
				break;
			}
		}
		cerr << ")";
#endif
		return out;
	}
	data_t _data = 0;
	constexpr data_t data() const{ return _data; }
#undef IS_INTEGRAL
#undef IS_UNSIGNED
};
template<class data_t, data_t _mod> vector<modular_fixed_base<data_t, _mod>> modular_fixed_base<data_t, _mod>::_INV;
template<class data_t, data_t _mod> modular_fixed_base<data_t, _mod> modular_fixed_base<data_t, _mod>::_primitive_root;

constexpr unsigned int mod = (119 << 23) + 1; // 998244353
// constexpr unsigned int mod = 1e9 + 7; // 1000000007
// constexpr unsigned int mod = 1e9 + 9; // 1000000009
// constexpr unsigned long long mod = (unsigned long long)1e18 + 9;
using modular = modular_fixed_base<decay_t<decltype(mod)>, mod>;

constexpr modular operator""_m(const char *x){
	modular res = 0;
	long long buffer = 0;
	long long buffer_width = 1;
	constexpr long long buffer_th = 1'000'000'000'000'000'000LL;
	while(*x){
		#ifdef LOCAL
		assert(isdigit(*x));
		#endif
		buffer = buffer * 10 + (*(x ++) - '0');
		if((buffer_width *= 10) == buffer_th){
			res = buffer_width * res + buffer;
			buffer = 0;
			buffer_width = 1;
		}
	}
	res = buffer_width * res + buffer;
	return res;
}

template<class T, size_t N, size_t M>
struct matrix_fixed_base{
	int n, m;
	array<array<T, M>, N> data;
	array<T, M> &operator[](int i){
		assert(0 <= i && i < n);
		return data[i];
	}
	const array<T, M> &operator[](int i) const{
		assert(0 <= i && i < n);
		return data[i];
	}
	matrix_fixed_base &inplace_slice(int il, int ir, int jl, int jr){
		assert(0 <= il && il <= ir && ir <= n);
		assert(0 <= jl && jl <= jr && jr <= m);
		n = ir - il, m = jr - jl;
		if(il > 0) for(auto i = 0; i < n; ++ i) swap(data[i], data[il + i]);
		data.resize(n);
		for(auto &row: data){
			row.erase(row.begin(), row.begin() + jl);
			row.resize(m);
		}
		return *this;
	}
	matrix_fixed_base slice(int il, int ir, int jl, int jr) const{
		return matrix_fixed_base(*this).inplace_slice(il, ir, jl, jr);
	}
	matrix_fixed_base &inplace_row_slice(int il, int ir){
		assert(0 <= il && il <= ir && ir <= n);
		n = ir - il;
		if(il > 0) for(auto i = 0; i < n; ++ i) swap(data[i], data[il + i]);
		data.resize(n);
		return *this;
	}
	matrix_fixed_base row_slice(int il, int ir) const{
		return matrix_fixed_base(*this).inplace_row_slice(il, ir);
	}
	matrix_fixed_base &inplace_column_slice(int jl, int jr){
		assert(0 <= jl && jl <= jr && jr <= m);
		m = jr - jl;
		for(auto &row: data){
			row.erase(row.begin(), row.begin() + jl);
			row.resize(m);
		}
		return *this;
	}
	matrix_fixed_base column_slice(int jl, int jr) const{
		return matrix_fixed_base(*this).inplace_column_slice(jl, jr);
	}
	bool operator==(const matrix_fixed_base &a) const{
		assert(n == a.n && m == a.m);
		return data == a.data;
	}
	bool operator!=(const matrix_fixed_base &a) const{
		assert(n == a.n && m == a.m);
		return data != a.data;
	}
	matrix_fixed_base &operator+=(const matrix_fixed_base &a){
		assert(n == a.n && m == a.m);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] += a[i][j];
		return *this;
	}
	matrix_fixed_base operator+(const matrix_fixed_base &a) const{
		return matrix_fixed_base(*this) += a;
	}
	matrix_fixed_base &operator-=(const matrix_fixed_base &a){
		assert(n == a.n && m == a.m);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] -= a[i][j];
		return *this;
	}
	matrix_fixed_base operator-(const matrix_fixed_base &a) const{
		return matrix_fixed_base(*this) -= a;
	}
	matrix_fixed_base &operator*=(const matrix_fixed_base &a){
		assert(m == a.n);
		int l = a.m;
		matrix_fixed_base res(n, l);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) for(auto k = 0; k < l; ++ k) res[i][k] += data[i][j] * a[j][k];
		return *this = res;
	}
	matrix_fixed_base operator*(const matrix_fixed_base &a) const{
		return matrix_fixed_base(*this) *= a;
	}
	matrix_fixed_base &operator*=(T c){
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] *= c;
		return *this;
	}
	matrix_fixed_base operator*(T c) const{
		return matrix_fixed_base(*this) *= c;
	}
	friend matrix_fixed_base operator*(T c, matrix_fixed_base a){
		for(auto i = 0; i < a.n; ++ i) for(auto j = 0; j < a.m; ++ j) a[i][j] = c * a[i][j];
		return a;
	}
	template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>
	matrix_fixed_base &inplace_power(U e){
		assert(n == m && e >= 0);
		matrix_fixed_base res(n, n, T{1});
		for(; e; *this *= *this, e >>= 1) if(e & 1) res *= *this;
		return *this = res;
	}
	template<class U>
	matrix_fixed_base power(U e) const{
		return matrix_fixed_base(*this).inplace_power(e);
	}
	matrix_fixed_base &inplace_transpose(){
		assert(n == m);
		for(auto i = 0; i < n; ++ i) for(auto j = i + 1; j < n; ++ j) swap(data[i][j], data[j][i]);
		return *this;
	}
	matrix_fixed_base transpose() const{
		if(n == m) return matrix_fixed_base(*this).inplace_transpose();
		matrix_fixed_base res(m, n);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) res[j][i] = data[i][j];
		return res;
	}
	vector<T> operator*(const vector<T> &v) const{
		assert(m == (int)v.size());
		vector<T> res(n, T{0});
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) res[i] += data[i][j] * v[j];
		return res;
	}
	friend vector<T> operator*(const vector<T> &v, const matrix_fixed_base &a){
		vector<T> res(a.m, T{0});
		for(auto i = 0; i < a.n; ++ i) for(auto j = 0; j < a.m; ++ j) res[j] += v[i] * a[i][j];
		return res;
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Otherwise, O(n * up_to * log(size)) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base &, T, int> inplace_REF(int up_to = -1){
		if(n == 0) return {*this, T{1}, 0};
		if(!~up_to) up_to = m;
		T det = 1;
		int rank = 0;
		for(auto j = 0; j < up_to; ++ j){
			if constexpr(is_floating_point_v<T>){
				static const T eps = 1e-9;
				int pivot = rank;
				for(auto i = rank + 1; i < n; ++ i) if(abs(data[pivot][j]) < abs(data[i][j])) pivot = i;
				if(rank != pivot){
					swap(data[rank], data[pivot]);
					det *= -1;
				}
				if(abs(data[rank][j]) <= eps) continue;
				det *= data[rank][j];
				T inv = 1 / data[rank][j];
				for(auto i = rank + 1; i < n; ++ i) if(abs(data[i][j]) > eps){
					T coef = data[i][j] * inv;
					for(auto k = j; k < m; ++ k) data[i][k] -= coef * data[rank][k];
				}
				++ rank;
			}
			else{
				for(auto i = rank + 1; i < n; ++ i) while(data[i][j]){
					T q;
					if constexpr(is_integral_v<T> || is_same_v<T, __int128_t> || is_same_v<T, __uint128_t>) q = data[rank][j] / data[i][j];
					else q = data[rank][j].data() / data[i][j].data();
					if(q) for(auto k = j; k < m; ++ k) data[rank][k] -= q * data[i][k];
					swap(data[rank], data[i]);
					det *= -1;
				}
				if(rank == j) det *= data[rank][j];
				else det = T(0);
				if(data[rank][j]) ++ rank;
			}
			if(rank == n) break;
		}
		return {*this, det, rank};
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Otherwise, O(n * up_to * log(size)) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base, T, int> REF(int up_to = -1) const{
		return matrix_fixed_base(*this).inplace_REF(up_to);
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base &, T, int> inplace_REF_field(int up_to = -1){
		if(n == 0) return {*this, T{1}, 0};
		if(!~up_to) up_to = m;
		T det = T{1};
		int rank = 0;
		for(auto j = 0; j < up_to; ++ j){
			int pivot = -1;
			for(auto i = rank; i < n; ++ i) if(data[i][j] != T(0)){
				pivot = i;
				break;
			}
			if(!~pivot){
				det = T(0);
				continue;
			}
			if(rank != pivot){
				swap(data[rank], data[pivot]);
				det *= -1;
			}
			det *= data[rank][j];
			T inv = 1 / data[rank][j];
			for(auto i = rank + 1; i < n; ++ i) if(data[i][j] != T(0)){
				T coef = data[i][j] * inv;
				for(auto k = j; k < m; ++ k) data[i][k] -= coef * data[rank][k];
			}
			++ rank;
			if(rank == n) break;
		}
		return {*this, det, rank};
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base, T, int> REF_field(int up_to = -1) const{
		return matrix_fixed_base(*this).inplace_REF_field(up_to);
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base &, T, int> inplace_RREF_field(int up_to = -1){
		if(n == 0) return {*this, T{1}, 0};
		auto [mat, det, rank] = inplace_REF_field(up_to);
		for(auto i = rank - 1; i >= 0; -- i){
			int pivot = find_if(mat[i].begin(), mat[i].end(), [&](const T &x){ return x != T{0}; }) - mat[i].begin();
			T inv = T{1} / mat[i][pivot];
			for(auto t = 0; t < i; ++ t){
				T coef = mat[t][pivot] * inv;
				for(auto j = 0; j < m; ++ j) mat[t][j] -= coef * mat[i][j];
			}
		}
		return {mat, det, rank};
	}
	// Assumes T is a field.
	// O(up_to) divisions with O(n * m * up_to) additions, subtractions, and multiplications.
	// Returns {REF matrix_fixed_base, determinant, rank}
	tuple<matrix_fixed_base, T, int> RREF_field(int up_to = -1) const{
		return matrix_fixed_base(*this).inplace_RREF_field(up_to);
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	// Otherwise, O(n^2 * log(size)) divisions with O(n^3) additions, subtractions, and multiplications.
	T determinant() const{
		assert(n == m);
		return get<1>(REF());
	}
	// Assumes T is a field.
	// O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	T determinant_field() const{
		assert(n == m);
		return get<1>(REF_field());
	}
	// Assumes T is either a floating, integral, or a modular type.
	// If T is a floating type, O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	// Otherwise, O(n^2 * log(size)) divisions with O(n^3) additions, subtractions, and multiplications.
	int rank() const{
		return get<2>(REF());
	}
	// Assumes T is a field.
	// O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	int rank_field() const{
		return get<2>(REF_field());
	}
	// Regarding the matrix as a system of linear equations by separating first m-1 columns,
	// find a solution of the system along with the basis for the nullspace
	// Assumes T is a field
	// O(n * m^2)
	optional<pair<vector<T>, vector<vector<T>>>> solve_right() const{
		assert(m >= 1);
		auto [rref, _, rank] = RREF_field(m - 1);
		for(auto i = rank; i < n; ++ i) if(rref[i][m - 1] != T{0}) return {};
		vector<T> res(m - 1);
		vector<int> pivot(rank), appear_as_pivot(m - 1);
		for(auto i = rank - 1; i >= 0; -- i){
			pivot[i] = find_if(rref[i].begin(), rref[i].end(), [&](const T &x){ return x != T{0}; }) - rref[i].begin();
			assert(pivot[i] < m - 1);
			appear_as_pivot[pivot[i]] = true;
			res[pivot[i]] = rref[i][m - 1] / rref[i][pivot[i]];
		}
		vector<vector<T>> basis;
		for(auto j = 0; j < m - 1; ++ j){
			if(appear_as_pivot[j]) continue;
			vector<T> b(m - 1);
			b[j] = T{1};
			for(auto i = 0; i < rank; ++ i){
				if(rref[i][j] == T{0}) continue;
				b[pivot[i]] = -rref[i][j] / rref[i][pivot[i]];
			}
			basis.push_back(b);
		}
		return pair{res, basis};
	}
	// Assumes T is a field.
	// O(n) divisions with O(n^3) additions, subtractions, and multiplications.
	optional<matrix_fixed_base> inverse() const{
		assert(n == m);
		if(n == 0) return *this;
		auto a = data;
		auto res = multiplicative_identity(n, m);
		for(auto j = 0; j < n; ++ j){
			int rank = j, pivot = -1;
			if constexpr(is_floating_point_v<T>){
				static const T eps = 1e-9;
				pivot = rank;
				for(auto i = rank + 1; i < n; ++ i) if(abs(a[pivot][j]) < abs(a[i][j])) pivot = i;
				if(abs(a[pivot][j]) <= eps) return {};
			}
			else{
				for(auto i = rank; i < n; ++ i) if(a[i][j] != T(0)){
					pivot = i;
					break;
				}
				if(!~pivot) return {};
			}
			swap(a[rank], a[pivot]), swap(res[rank], res[pivot]);
			T inv = 1 / a[rank][j];
			for(auto k = 0; k < n; ++ k) a[rank][k] *= inv, res[rank][k] *= inv;
			for(auto i = 0; i < n; ++ i){
				if constexpr(is_floating_point_v<T>){
					static const T eps = 1e-9;
					if(i != rank && abs(a[i][j]) > eps){
						T d = a[i][j];
						for(auto k = 0; k < n; ++ k) a[i][k] -= d * a[rank][k], res[i][k] -= d * res[rank][k];
					}
				}
				else if(i != rank && a[i][j] != T(0)){
					T d = a[i][j];
					for(auto k = 0; k < n; ++ k) a[i][k] -= d * a[rank][k], res[i][k] -= d * res[rank][k];
				}
			}
		}
		return res;
	}
	matrix_fixed_base &operator/=(const matrix_fixed_base &otr){
		return *this *= *otr.inverse();
	}
	matrix_fixed_base operator/(const matrix_fixed_base &otr) const{
		return matrix_fixed_base(*this) /= otr;
	}
	matrix_fixed_base &operator/=(const T &c){
		return *this *= T{1} / c;
	}
	matrix_fixed_base operator/(const T &c) const{
		return matrix_fixed_base(*this) /= c;
	}
	// O(n * 2^n)
	T permanent() const{
		assert(n <= 30 && n == m);
		T perm = n ? 0 : 1;
		array<T, N> sum;
		sum.fill(T{0});
		for(auto order = 1; order < 1 << n; ++ order){
			int j = __lg(order ^ order >> 1 ^ order - 1 ^ order - 1 >> 1), sign = (order ^ order >> 1) & 1 << j ? 1 : -1;
			T prod = order & 1 ? -1 : 1;
			if((order ^ order >> 1) & 1 << j) for(auto i = 0; i < n; ++ i) prod *= sum[i] += data[i][j];
			else for(auto i = 0; i < n; ++ i) prod *= sum[i] -= data[i][j];
			perm += prod;
		}
		return perm * (n & 1 ? -1 : 1);
	}
	template<class output_stream>
	friend output_stream &operator<<(output_stream &out, const matrix_fixed_base &a){
		out << "\n";
		for(auto i = 0; i < a.n; ++ i){
			for(auto j = 0; j < a.m; ++ j) out << a[i][j] << " ";
			out << "\n";
		}
		return out;
	}
	matrix_fixed_base(int n, int m, T init_diagonal = T{0}, T init_off_diagonal = T{0}): n(n), m(m){
		assert(0 <= n && n <= N && 0 <= m && m <= M);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] = i == j ? init_diagonal : init_off_diagonal;
	}
	matrix_fixed_base(int n, int m, const array<array<T, M>, N> &a): n(n), m(m), data(a){ assert(0 <= n && n <= N && 0 <= m && m <= M); }
	matrix_fixed_base(int n, int m, const array<T, N * M> &a): n(n), m(m){
		assert(0 <= n && n <= N && 0 <= m && m <= M);
		for(auto i = 0; i < n; ++ i) for(auto j = 0; j < m; ++ j) data[i][j] = a[m * i + j];
	}
	static matrix_fixed_base additive_identity(int n, int m){
		return matrix_fixed_base(n, m, T{0}, T{0});
	}
	static matrix_fixed_base multiplicative_identity(int n, int m){
		return matrix_fixed_base(n, m, T{1}, T{0});
	}
};

template<class T>
using matrix = matrix_fixed_base<T, 3, 3>;

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
	using M = matrix<modular>;
	auto read = [&]()->M{
		M mat(2, 2);
		for(auto i = 0; i < 2; ++ i){
			for(auto j = 0; j < 2; ++ j){
				cin >> mat[i][j];
			}
		}
		return mat;
	};
	auto write = [&](M mat)->void{
		for(auto i = 0; i < 2; ++ i){
			for(auto j = 0; j < 2; ++ j){
				cout << mat[i][j] << " ";
			}
		}
	};
	int n, qn;
	cin >> n >> qn;
	vector<M> a(n, M(2, 2));
	for(auto i = 0; i < n; ++ i){
		a[i] = read();
	}
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
			write(a[u]);
			cout << "\n";
		}
		else if(op == "query_path"){
			int u, v;
			cin >> u >> v;
			assert(connected(u, v));
			df.dfs(g, {v});
			M res = a[u];
			while(u != v){
				u = df.pv[u];
				res *= a[u];
			}
			write(res);
			cout << "\n";
		}
		else if(op == "query_subtree"){
			int u;
			cin >> u;
			df.dfs(g, {find_root(u)});
			M res = M::multiplicative_identity(2, 2);
			for(auto i = df.pos[u]; i < df.end[u]; ++ i){
				res *= a[df.order[i]];
			}
			write(res);
			cout << "\n";
		}
		else if(op == "set"){
			int u;
			cin >> u;
			a[u] = read();
		}
		else if(op == "update"){
			int u;
			cin >> u;
			auto f = read();
			a[u] = f * a[u] / f;
		}
		else if(op == "update_path"){
			int u, v;
			cin >> u >> v;
			assert(connected(u, v));
			df.dfs(g, {v});
			auto f = read();
			a[u] = f * a[u] / f;
			while(u != v){
				u = df.pv[u];
				a[u] = f * a[u] / f;
			}
		}
		else if(op == "update_subtree"){
			int u;
			cin >> u;
			auto f = read();
			df.dfs(g, {find_root(u)});
			for(auto i = df.pos[u]; i < df.end[u]; ++ i){
				a[df.order[i]] = f * a[df.order[i]] / f;
			}
		}
		else{
			assert(false);
		}
	}
	return 0;
}

/*

*/
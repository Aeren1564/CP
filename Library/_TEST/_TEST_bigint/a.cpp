#include <bits/stdc++.h>
using namespace std;
#if __cplusplus > 201703L
#include <ranges>
using namespace numbers;
#endif

// Internally, the numbers are stored in binary in little endian order.
// Negative numbers are assumed to have infinite leading ones, represented in two's complement.
// No leading ~0 allowed for negative numbers, and no leading 0 allowed for non-negative numbers. This ensures that each integer has a unique representation.
#include <x86intrin.h>
struct bigint{
	using T = unsigned long long;
	using T_large = __uint128_t;
	static constexpr signed int width = 8 * sizeof(T);
	static constexpr T pad[2] = {T(0), ~T(0)};
	bool sign = 0; // 0 (non-negative), 1 (negative)
	vector<T> data;
	void _trim(){
		while(!data.empty() && data.back() == pad[sign]) data.pop_back();
	}
	bool _is_valid() const{
		return data.empty() || data.back() != pad[sign];
	}
	// Assumes x is non-zero
	static void _negate(vector<T> &x){
		for(auto &d: x) d = ~d;
		int i = 0;
		while(i < (int)x.size() && !~x[i]) x[i ++] = 0;
		if(i == (int)x.size()) x.push_back(1);
		else ++ x[i];
	}
	static void _add_apply(bool &xsign, vector<T> &x, bool ysign, const vector<T> &y){
		if(x.size() < y.size()) x.resize(y.size(), pad[xsign]);
		unsigned char carry = 0;
		for(auto i = 0; i < (int)y.size(); ++ i) carry = _addcarry_u64(carry, x[i], y[i], &x[i]);
		for(auto i = (int)y.size(); i < (int)x.size() && carry != ysign; ++ i) carry = _addcarry_u64(carry, x[i], pad[ysign], &x[i]);
		if(carry != ysign){
			if(xsign == ysign) x.push_back(pad[xsign] << 1 | carry);
			else xsign = !xsign;
		}
	}
	static void _subtract_apply(bool &xsign, vector<T> &x, bool ysign, const vector<T> &y){
		if(x.size() < y.size()) x.resize(y.size(), pad[xsign]);
		unsigned char borrow = 0;
		for(auto i = 0; i < (int)y.size(); ++ i) borrow = _subborrow_u64(borrow, x[i], y[i], &x[i]);
		for(auto i = (int)y.size(); i < (int)x.size() && borrow != ysign; ++ i) borrow = _subborrow_u64(borrow, x[i], pad[ysign], &x[i]);
		if(borrow != ysign){
			if(xsign == ysign) xsign = !xsign;
			else x.push_back(pad[xsign] ^ 1);
		}
	}
	// Assumes both x and y are positive.
	static vector<T> _naive_multiplication(const vector<T> &x, const vector<T> &y){
		if(x.empty() || y.empty()) return {};
		vector<T> z(x.size() + y.size() - 1);
		for(auto i = 0; i < (int)x.size(); ++ i) for(auto j = 0; j < (int)y.size(); ++ j){
			T_large rem = (T_large)x[i] * y[j];
			for(auto k = i + j; rem; ++ k){
				if((int)z.size() <= k) z.push_back(0);
				rem += z[k];
				z[k] = rem & ~T(0);
				rem >>= width;
			}
		}
		return z;
	}
	// TODO: implement Karatsuba, Toom-Cook, and Schönhage–Strassen
	static vector<T> _multiply(const vector<T> &x, const vector<T> &y){
		return _naive_multiplication(x, y);
	}
	bigint(){ }
	bigint(const string &s, unsigned int base = 2){
		if(base == 2){
			int pos = 0;
			while(pos < (int)s.size() && (s[pos] == '-' || s[pos] == '+')){
				if(s[pos] == '-') sign = !sign;
				++ pos;
			}
			for(auto i = (int)s.size() - 1; i >= pos; i -= width){
				T x = 0;
				for(auto j = max(pos, i - width + 1); j <= i; ++ j){
					assert('0' <= s[j] && s[j] <= '1');
					x = x << 1 | s[j] - '0';
				}
				data.push_back(x);
			}
			while(!data.empty() && !data.back()) data.pop_back();
			if(sign){
				if(data.empty()) sign = 0;
				else _negate(data);
			}
			_trim();
		}
		else assert(false);
		assert(_is_valid());
	}
	template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>
	bigint(U x){
		if(x < 0){
			*this = -bigint(-x);
			return;
		}
		while(x){
			data.push_back(x & ~T(0));
			x /= T_large(1) << width;
		}
	}
	friend istream &operator>>(istream &in, bigint &x){
		string s;
		in >> s;
		x = bigint(s);
		return in;
	}
	friend ostream &operator<<(ostream &out, const bigint &x){
		if(!x) return out << '0';
		if(!x.sign){
			assert(x.data.back());
			for(int i = __lg(x.data.back()); i >= 0; -- i) out << (x.data.back() >> i & 1);
			for(auto i = (int)x.data.size() - 2; i >= 0; -- i) out << bitset<width>(x.data[i]);
			return out;
		}
		else return out << '-' << -x;
	}
	// TODO: Implement Schoenhage
	friend string to_string(const bigint &x, unsigned int base = 2){
		if(base == 2){
			stringstream ss;
			ss << x;
			string s;
			ss >> s;
			return s;
		}
		else assert(false);
	}
	operator bool() const{
		return sign || !data.empty();
	}
	template<class U, typename enable_if<is_integral<U>::value && !is_same<U, bool>::value>::type* = nullptr>
	operator U() const{
		U x = 0;
		if(!sign) for(auto i = (int)data.size() - 1; i >= 0; -- i) x = x << width | data[i];
		else x = -U(*this);
		return x;
	}
	bool operator==(const bigint &x) const{ return sign == x.sign && data == x.data; }
	bool operator!=(const bigint &x) const{ return !(*this == x); }
	bool operator<(const bigint &x) const{
		if(sign != x.sign) return sign > x.sign;
		if(!*this) return false;
		if(data.size() != x.data.size()) return data.size() < x.data.size() ^ sign;
		for(auto i = (int)data.size() - 1; i >= 0; -- i) if(data[i] != x.data[i]) return data[i] < x.data[i];
		return false;
	}
	bool operator<=(const bigint &x) const{ return !(x < *this); }
	bool operator>=(const bigint &x) const{ return !(*this < x); }
	bool operator>(const bigint &x) const{ return x < *this; }
#define COMPARE_OP(OP)\
template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>\
bool operator OP(U x) const{\
	return *this OP bigint(x);\
}\
template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>\
friend bool operator OP(U x, const bigint &y){\
	return bigint(x) OP y;\
}
COMPARE_OP(==) COMPARE_OP(!=) COMPARE_OP(<) COMPARE_OP(<=) COMPARE_OP(>=) COMPARE_OP(>)
#undef COMPARE_OP
	bigint &operator&=(const bigint &x){
		if(data.size() < x.data.size()) data.resize(x.data.size(), pad[sign]);
		for(auto i = 0; i < (int)x.data.size(); ++ i) data[i] &= x.data[i];
		if(!x.sign) data.resize(x.data.size());
		sign &= x.sign;
		_trim();
		return *this;
	}
	bigint operator&(const bigint &x) const{
		return bigint(*this) &= x;
	}
	bigint &operator|=(const bigint &x){
		if(data.size() < x.data.size()) data.resize(x.data.size(), pad[sign]);
		for(auto i = 0; i < (int)x.data.size(); ++ i) data[i] |= x.data[i];
		if(x.sign) data.resize(x.data.size());
		sign |= x.sign;
		_trim();
		return *this;
	}
	bigint operator|(const bigint &x) const{
		return bigint(*this) |= x;
	}
	bigint &operator^=(const bigint &x){
		if(data.size() < x.data.size()) data.resize(x.data.size(), pad[sign]);
		for(auto i = 0; i < (int)x.data.size(); ++ i) data[i] ^= x.data[i];
		if(x.sign) for(auto i = (int)x.data.size(); i < (int)data.size(); ++ i) data[i] = ~data[i];
		sign ^= x.sign;
		_trim();
		return *this;
	}
	bigint operator^(const bigint &x) const{
		return bigint(*this) ^= x;
	}
	bigint operator+() const{
		return *this;
	}
	bigint operator-() const{
		if(!*this) return *this;
		bigint x(*this);
		x.sign = !x.sign;
		_negate(x.data);
		x._trim();
		return x;
	}
	friend bigint abs(bigint x){
		return x.sign ? -x : x;
	}
	bigint &operator+=(const bigint &x){
		if(!x) return *this;
		if(!*this) return *this = x;
		_add_apply(sign, data, x.sign, x.data);
		_trim();
		return *this;
	}
	bigint operator+(const bigint &x) const{
		return bigint(*this) += x;
	}
	bigint &operator-=(const bigint &x){
		if(!x) return *this;
		if(!*this) return *this = -x;
		_subtract_apply(sign, data, x.sign, x.data);
		_trim();
		return *this;
	}
	bigint operator-(const bigint &x) const{
		return bigint(*this) -= x;
	}
	bigint &operator++(){
		unsigned char carry = 1;
		for(auto i = 0; i < (int)data.size() && carry; ++ i) carry = _addcarry_u64(carry, data[i], 0ULL, &data[i]);
		if(carry){
			if(!sign) data.push_back(1);
			else sign = !sign;
		}
		_trim();
		return *this;
	}
	bigint operator++(int){
		bigint x = *this;
		++ *this;
		return x;
	}
	bigint &operator--(){
		unsigned char borrow = 1;
		for(auto i = 0; i < (int)data.size() && borrow; ++ i) borrow = _subborrow_u64(borrow, data[i], 0ULL, &data[i]);
		if(borrow){
			if(!sign) sign = !sign;
			else data.push_back(pad[sign] ^ 1);
		}
		_trim();
		return *this;
	}
	bigint operator--(int){
		bigint x = *this;
		-- *this;
		return x;
	}
	bigint &operator*=(const bigint &x){
		if(!*this || !x) return *this = bigint();
		data = _multiply(abs(*this).data, abs(x).data);
		sign ^= x.sign;
		if(sign) _negate(data);
		_trim();
		return *this;
	}
	bigint operator*(const bigint &x) const{
		return bigint(*this) *= x;
	}
	template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>
	bigint &inplace_power(U e){
		assert(e >= 0);
		bigint res(1);
		for(; e; e >>= 1, *this *= *this) if(e & 1) res *= *this;
		return *this = res;
	}
	template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>
	bigint power(U e) const{
		return bigint(*this).inplace_power(e);
	}
	static pair<vector<T>, T> small_div(const vector<T> &x, T y){
		assert(y);
		T_large rem = 0;
		vector<T> q((int)x.size());
		for(auto i = (int)x.size() - 1; i >= 0; -- i){
			rem = rem << width | x[i];
			q[i] = rem / y;
			rem = rem % y;
		}
		return {q, rem};
	}
	// Todo: Implement Burnikel-Ziegler
	// Assumes x is non-negative and y is positive
	// Returns {quotient, remainder} pair
	static pair<vector<T>, vector<T>> large_div(const vector<T> &x, const vector<T> &y){
		assert(!y.empty());
		int m = (int)x.size(), n = (int)y.size();
		if(m < n) return {{}, x};
		if(n == 1){
			auto [q, r] = small_div(x, y[0]);
			return {q, {r}};
		}
		vector<T> q(m - n + 1), r(n), xn(m + 1), yn(n);
		T_large qhat, rhat, p;
		int s = __builtin_clzll(y[n - 1]);
		for(auto i = n - 1; i > 0; -- i) yn[i] = y[i] << s | (T_large)y[i - 1] >> width - s;
		yn[0] = y[0] << s;
		xn[m] = (T_large)x[m - 1] >> width - s;
		for(auto i = m - 1; i > 0; -- i) xn[i] = x[i] << s | (T_large)x[i - 1] >> width - s;
		xn[0] = x[0] << s;
		__int128_t t, k;
		static const T_large base = T_large(1) << width;
		for(auto j = m - n; j >= 0; -- j){
			qhat = (xn[j + n] * base + xn[j + n - 1]) / yn[n - 1];
			rhat = (xn[j + n] * base + xn[j + n - 1]) % yn[n - 1];
			FLAG:
			if(qhat >= base || (T)qhat * (T_large)yn[n - 2] > base * rhat + xn[j + n - 2]){
				-- qhat;
				rhat += yn[n - 1];
				if(rhat < base) goto FLAG;
			}
			k = 0;
			for(auto i = 0; i < n; ++ i){
				p = (T)qhat * (T_large)yn[i];
				t = xn[i + j] - k - (p & base - 1);
				xn[i + j] = t;
				k = (p >> width) - (t >> width);
			}
			t = xn[j + n] - k;
			xn[j + n] = t;
			q[j] = qhat;
			if(t < 0){
				-- q[j];
				k = 0;
				for(auto i = 0; i < n; ++ i){
					t = (T_large)xn[i + j] + yn[i] + k;
					xn[i + j] = t;
					k = t >> width;
				}
				xn[j + n] += k;
			}
		}
		if(!r.empty()){
			for(auto i = 0; i < n - 1; ++ i) r[i] = xn[i] >> s | (T_large)xn[i + 1] << width - s;
			r[n - 1] = xn[n - 1] >> s;
		}
		return {q, r};
	}
	friend pair<bigint, bigint> bigint_div(const bigint &x, const bigint &y){
		assert(y);
		bigint q, r;
		tie(q.data, r.data) = large_div(abs(x).data, abs(y).data);
		q.sign = x.sign ^ y.sign;
		r.sign = x.sign;
		while(!q.data.empty() && !q.data.back()) q.data.pop_back();
		if(q.data.empty()) q.sign = 0;
		else if(q.sign) _negate(q.data);
		while(!r.data.empty() && !r.data.back()) r.data.pop_back();
		if(r.data.empty()) r.sign = 0;
		else if(r.sign) _negate(r.data);
		q._trim();
		r._trim();
		if(x.sign != y.sign && r){
			-- q;
			r += y;
		}
		return {q, r};
	}
	bigint &operator/=(const bigint &x){
		return *this = bigint_div(*this, x).first;
	}
	bigint operator/(const bigint &x) const{
		return bigint(*this) /= x;
	}
	bigint &operator%=(const bigint &x){
		return *this = bigint_div(*this, x).second;
	}
	bigint operator%(const bigint &x) const{
		return bigint(*this) %= x;
	}
#define BINARY_OP(APPLY_OP, OP)\
template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>\
bigint &operator APPLY_OP(U x){\
	return *this APPLY_OP bigint(x);\
}\
template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>\
bigint operator OP(U x) const{\
	return bigint(*this) APPLY_OP bigint(x);\
}\
template<class U, typename enable_if<is_integral<U>::value>::type* = nullptr>\
friend bigint operator OP(U x, const bigint &y){\
	return bigint(y) APPLY_OP bigint(x);\
}
BINARY_OP(&=, &) BINARY_OP(|=, |) BINARY_OP(^=, ^) BINARY_OP(+=, +) BINARY_OP(-=, -) BINARY_OP(*=, *) BINARY_OP(/=, /) BINARY_OP(%=, %)
#undef BINARY_OP
	friend bigint gcd(const bigint &x, const bigint &y){
		if(x.sign || y.sign) return gcd(abs(x), abs(y));
		return y ? gcd(y, x % y) : x;
	}
	friend bigint lcm(const bigint &x, const bigint &y){
		if(x.sign || y.sign) return lcm(abs(x), abs(y));
		return x / gcd(x, y) * y;
	}
	template<class Iter>
	static bigint sum(Iter begin, Iter end){
		int n = end - begin;
		vector<bigint> temp(n << 1);
		for(auto i = 0; i < n; ++ i) temp[n + i] = *(begin + i);
		for(auto i = n - 1; i >= 1; -- i) temp[i] = temp[i << 1] + temp[i << 1 | 1];
		bigint res = 0;
		for(auto l = n, r = n << 1; l < r; l >>= 1, r >>= 1){
			if(l & 1) res += temp[l ++];
			if(r & 1) res += temp[-- r];
		}
		return res;
	}
	template<class Iter>
	static bigint product(Iter begin, Iter end){
		int n = end - begin;
		vector<bigint> temp(n << 1);
		for(auto i = 0; i < n; ++ i) temp[n + i] = *(begin + i);
		for(auto i = n - 1; i >= 1; -- i) temp[i] = temp[i << 1] * temp[i << 1 | 1];
		bigint res = 1;
		for(auto l = n, r = n << 1; l < r; l >>= 1, r >>= 1){
			if(l & 1) res *= temp[l ++];
			if(r & 1) res *= temp[-- r];
		}
		return res;
	}
#if __cplusplus > 201703L
	template<ranges::random_access_range R>
	static bigint sum(R &&r){
		return sum(r.begin(), r.end());
	}
	template<ranges::random_access_range R>
	static bigint product(R &&r){
		return product(r.begin(), r.end());
	}
#endif
};

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	bigint x, y;
	cin >> x >> y;
	
	cout << x ++ << endl;
	
	cout << ++ x << endl;
	
	cout << x -- << endl;
	
	cout << -- x << endl;

	cout << (x & y) << endl;

	cout << (x | y) << endl;

	cout << (x ^ y) << endl;

	cout << x + y << endl;

	cout << x - y << endl;

	cout << x * y << endl;

	if(y){
		cout << x / y << endl;

		cout << x % y << endl;
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
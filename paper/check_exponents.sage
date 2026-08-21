# Sage verification of the row-exponent identity (Proposition 4.3)
# and the appendix exponent identity (A.15).
#
# Run: sage check_exponents.sage
# Expected output: both differences are 0.

var('r t ell k n p')
C2 = lambda z: z*(z-1)/2
B = n + p
Delta = p*(2*n + p)
N = n*Delta
A0 = n*p*(2*n + p + 1)/2
s = n*ell + t

# Proposition 4.3: row-exponent identity
lhs = n*C2(t) + n*C2(r+B*ell) + B*t*(r+B*ell) + N*C2(k) + ell*(N*(k-1) + A0 - t*Delta)
rhs = n*C2(r) + B*r*s + n*C2(s) + N*C2(k+ell)
print("Proposition 4.3 difference:", expand(lhs - rhs))

# Appendix (A.15): full exponent identity
var('rho sigma iota eta')
R = rho + n*iota + B*eta - n*ell
S = sigma - n*iota - n*eta + B*ell
w = ell - iota - eta
H = lambda X,Y: n*C2(X) + B*X*Y + n*C2(Y)
E = (H(rho,sigma) + n*p^2*C2(iota) + n*p*(sigma-rho-n)*iota
     + (Delta*sigma - A0)*eta
     + (p*Delta*eta + Delta*rho + A0 - n*p)*ell)
print("Appendix (A.15) difference:", expand(E - H(R,S) - N*C2(w+1)))

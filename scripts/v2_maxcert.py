"""Rigorous (ball-arithmetic, python-flint/Arb) certificate that |omega1|^2 attains its global
maximum 144 over R^3 at the origin (and only there).  By the exact axisymmetry and evenness shown in
v2_symbolic.py it suffices to treat G(x,z) = |omega1|^2(x,0,z) on [0,1]^2 (G = 0 when x^2+z^2 >= 1).
G = Q(x,z,t) * beta^2, t = 1/(1-rho), rho = x^2+z^2, beta = exp(-3 rho t).
Regions:
 (I)  [-h,h]^2: Hessian of G negative definite at every point (interval check) => G strictly concave
      there, grad G(0)=0 => G < G(0) on the box minus origin.
 (II) boxes meeting rho <= 1-eta, outside (I): interval upper bound of G < 144.
 (III) rho in [1-eta, 1): G <= K t^D exp(-6(t-1)) with t >= 1/eta, explicit (see below) < 144.
"""
import sympy as sp, pickle, sys
from flint import arb, arb_series
from fractions import Fraction as Fr
x,z,t = sp.symbols('x z t', real=True)
d = pickle.load(open('v2_sym.pkl','rb'))
y = sp.Symbol('y', real=True)
G = sp.expand(d['G'])
c=3
def D(P,v,m):
    return sp.expand(sp.diff(P,v) + 2*v*t**2*(sp.diff(P,t) - m*c*P))
Gxx=D(D(G,x,2),x,2); Gzz=D(D(G,z,2),z,2); Gxz=D(D(G,x,2),z,2)
print("grad G(0):", D(G,x,2).subs({x:0,z:0,t:1}), D(G,z,2).subs({x:0,z:0,t:1}))
print("Hessian(0):", Gxx.subs({x:0,z:0,t:1}), Gxz.subs({x:0,z:0,t:1}), Gzz.subs({x:0,z:0,t:1}))
def mkf(P):
    P = sp.Poly(P, x, z, t)
    terms=[(m, int(cf.p), int(cf.q)) for m,cf in P.terms()]
    def f(X,Z,T):
        s=arb(0)
        for (i,j,k),p,q in terms:
            s += arb(p)/q * X**i * Z**j * T**k
        return s
    return f
fQ=mkf(G); fxx=mkf(Gxx); fzz=mkf(Gzz); fxz=mkf(Gxz)
def iv(a,b): return arb((Fr(a)+Fr(b))/2 if False else (a+b)/2, (b-a)/2)
def box_vals(a0,a1,b0,b1):
    X=arb.union(arb(a0),arb(a1)) if hasattr(arb,'union') else None
    return X
def fa(q):
    q=Fr(q); return arb(q.numerator)/q.denominator
def A(lo,hi):
    return fa(lo).union(fa(hi))
def rho_range(a0,a1,b0,b1):  # a,b >=0 boxes
    return a0*a0+b0*b0, a1*a1+b1*b1
# (I) local concavity
h = Fr(1,8)
def local_ok(a0,a1,b0,b1,depth=0):
    X=A(a0,a1); Z=A(b0,b1); R=X*X+Z*Z; T=1/(1-R); B2=(-6*R*T).exp()
    H11=fxx(X,Z,T)*B2; H22=fzz(X,Z,T)*B2; H12=fxz(X,Z,T)*B2
    det=H11*H22-H12*H12
    if H11<0 and H22<0 and det>0: return 1
    if depth>12: raise SystemExit("local concavity check failed")
    am=(a0+a1)/2; bm=(b0+b1)/2
    return sum(local_ok(p,q,r,s,depth+1) for p,q in ((a0,am),(am,a1)) for r,s in ((b0,bm),(bm,b1)))
nloc=local_ok(Fr(-1,8),Fr(1,8),Fr(-1,8),Fr(1,8))
print("(I) concavity verified on [-1/8,1/8]^2 with", nloc, "boxes")
# (III) tail: rho >= 1-eta  => t >= 1/eta
eta=Fr(1,20); T0=1/eta
Pt=sp.Poly(G, x, z, t)
# |Q| <= sum |coef| t^k  for |x|,|z|<=1, t>=1 ; collect by power of t
K={}
for (i,j,k),cf in Pt.terms(): K[k]=K.get(k,0)+abs(Fr(int(cf.p),int(cf.q)))
Dg=max(K); Ksum=sum(K.values())
# for t>=T0>=1: |Q| <= Ksum t^Dg ; beta^2 = exp(-6 rho t) = exp(-6(t-1)); t^Dg e^{-6(t-1)} decreasing for t>=Dg/6
assert T0>=Fr(Dg,6)
tail = fa(Ksum)*fa(T0)**Dg*(-6*(fa(T0)-1)).exp()
print("(III) tail bound for rho>=1-eta (eta=1/20): G <=", tail.upper(), " (<144:", tail<144,")")
assert tail<144
# (II) branch and bound on [0,1]^2 outside [0,1/8]^2
cnt=[0]
def bb(a0,a1,b0,b1,depth=0):
    if a1<=h and b1<=h: return  # inside region (I)
    r0,r1=rho_range(a0,a1,b0,b1)
    if r0>=1-eta: return        # region (III)
    if r1<1:
        X=A(a0,a1); Z=A(b0,b1); R=X*X+Z*Z; T=1/(1-R)
        val=fQ(X,Z,T)*(-6*R*T).exp()
        cnt[0]+=1
        if val<144: return
    if depth>40: raise SystemExit(f"bb failed at {a0},{a1},{b0},{b1}")
    am=(a0+a1)/2; bm=(b0+b1)/2
    for p,q in ((a0,am),(am,a1)):
        for r,s in ((b0,bm),(bm,b1)): bb(p,q,r,s,depth+1)
sys.setrecursionlimit(10000)
bb(Fr(0),Fr(1),Fr(0),Fr(1))
print("(II) verified G<144 on all remaining boxes;", cnt[0], "interval evaluations")
print("CERTIFIED: max |omega1|^2 = 144 attained only at the origin; M_1 = ||omega1||_inf = 12")

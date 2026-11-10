"""Exact symbolic computations for the localized field (V2 construction).
beta(rho) = exp(-c*rho/(1-rho)) for rho=|x|^2<1, 0 otherwise (C^infinity, support = closed unit ball).
Psi = beta*e_z + eps*z*beta*(-y, x, 0);  u1 = curl Psi;  omega1 = curl u1.
Every derivative of P(x,y,z,t)*beta^m (t = 1/(1-rho)) is again Q(x,y,z,t)*beta^m with Q polynomial:
 d/dx_i (P beta^m) = (dP/dx_i + 2 x_i t^2 (dP/dt - m c P)) beta^m, since d(beta)/d(rho) = -c t^2 beta, dt/drho = t^2."""
import sympy as sp, pickle
x,y,z,t = sp.symbols('x y z t', real=True)
c = sp.Integer(3); eps = sp.Integer(1)
X=(x,y,z)
def D(P,i,m=1):
    xi=X[i]; return sp.expand(sp.diff(P,xi) + 2*xi*t**2*(sp.diff(P,t) - m*c*P))
def curl(F,m=1): return [D(F[2],1,m)-D(F[1],2,m), D(F[0],2,m)-D(F[2],0,m), D(F[1],0,m)-D(F[0],1,m)]
Psi = [-eps*y*z, eps*x*z, sp.Integer(1)]          # times beta
u = curl(Psi)                                        # times beta
w = curl(u)                                          # times beta
divu = sp.expand(sum(D(u[i],i) for i in range(3)))
print("div u1 (coefficient of beta) =", divu)
Q = sp.expand(sum(wi**2 for wi in w))               # |omega1|^2 = Q * beta^2
# axisymmetry: Q invariant under rotation about z-axis
cs, sn = sp.symbols('cs sn', real=True)
Qr = sp.expand(Q.subs({x: cs*x - sn*y, y: sn*x + cs*y}, simultaneous=True))
diff = sp.expand(Qr - Q)
red = sp.expand(sp.Poly(diff, cs, sn).as_expr())
# reduce using sn^2 = 1 - cs^2
red = sp.expand(red.subs(sn**2, 1-cs**2))
for k in range(2, 12):
    red = sp.expand(red.subs(sn**k, sn**(k%2)*(1-cs**2)**(k//2)))
print("rotation-invariance residual (mod cs^2+sn^2=1):", sp.simplify(red))
print("evenness: Q(-x)-Q =", sp.expand(Q.subs(x,-x)-Q), "; Q(-z)-Q =", sp.expand(Q.subs(z,-z)-Q))
o={x:0,y:0,z:0,t:1}
print("omega1(0) =", [wi.subs(o) for wi in w], " (beta(0)=1)")
print("u1(0) =", [ui.subs(o) for ui in u])
grad=[[D(u[i],j).subs(o) for j in range(3)] for i in range(3)]
print("grad u1(0) =", grad)
lapw=[sp.expand(sum(D(D(wi,j),j) for j in range(3))).subs(o) for wi in w]
print("Laplacian omega1(0) =", lapw)
G = sp.expand(Q.subs(y,0))   # |omega1|^2 on plane y=0, times beta^2
pickle.dump({'G':G,'w':w,'u':u}, open('v2_sym.pkl','wb'))
print("G(0)=", G.subs({x:0,z:0,t:1}), " deg in t:", sp.Poly(G,t).degree())

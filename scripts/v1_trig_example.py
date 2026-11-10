"""Exact symbolic verification of the V1 counterexample field (sympy).
U = a(-sin y, sin x, 0) + (-sin x cos z, 0, cos x sin z), a = 3, u0 = A*U on T^3=(R/2piZ)^3."""
import sympy as sp
x,y,z,A,nu,a = sp.symbols('x y z A nu a', real=True)
X=(x,y,z)
U = sp.Matrix([-a*sp.sin(y) - sp.sin(x)*sp.cos(z), a*sp.sin(x), sp.cos(x)*sp.sin(z)])
div = sp.simplify(sum(sp.diff(U[i],X[i]) for i in range(3)))
def curl(F): return sp.Matrix([sp.diff(F[2],y)-sp.diff(F[1],z), sp.diff(F[0],z)-sp.diff(F[2],x), sp.diff(F[1],x)-sp.diff(F[0],y)])
W = sp.simplify(curl(U))
print("div U =", div)
print("Omega = curl U =", list(W))
W2 = sp.expand(sum(w**2 for w in W))
print("|Omega|^2 =", W2)
grad = sp.Matrix(3,3,lambda i,j: sp.diff(U[i],X[j]))
S = (grad+grad.T)/2
o = {x:0,y:0,z:0}
print("Omega(0) =", list(W.subs(o)), " S(0) =", S.subs(o).tolist(), " U(0) =", list(U.subs(o)))
lap = lambda f: sum(sp.diff(f,v,2) for v in X)
# vorticity equation RHS for u = A U (omega = A Omega): A^2[(Om.grad)U - (U.grad)Om] + nu A Lap Om
stretch = sp.Matrix([sum(W[j]*sp.diff(U[i],X[j]) for j in range(3)) for i in range(3)])
adv = sp.Matrix([sum(U[j]*sp.diff(W[i],X[j]) for j in range(3)) for i in range(3)])
rhs = A**2*(stretch-adv) + nu*A*sp.Matrix([lap(w) for w in W])
r0 = sp.simplify(rhs.subs(o))
print("d/dt omega at x*=0, t=0:", list(r0))
xi = W.subs(o)/sp.sqrt(sum(w**2 for w in W.subs(o)))
rate = sp.factor(sp.simplify((xi.T*r0)[0].subs(a,3)))
print("a=3: d/dt |omega(0,t)| at t=0 =", rate, "; M0 = |A Omega(0)| =", sp.simplify(A*sp.sqrt(sum(w**2 for w in W.subs(o))).subs(a,3)))
# max certificate: |Omega|^2 with cx=cos x etc.
cx,cy,sx,sz=sp.symbols('cx cy sx sz',real=True)
print("|Omega|^2 in terms of trig (should be a^2(cx+cy)^2+4 sx^2 sz^2):",
      sp.simplify(W2 - (a**2*(sp.cos(x)+sp.cos(y))**2 + 4*sp.sin(x)**2*sp.sin(z)**2)))
# 4a^2 - |Omega|^2 >= 4a^2 - a^2(cx+1)^2 - 4(1-cx^2) = (1-cx)[(a^2-4)(1+cx)... ] check
expr = sp.factor(4*a**2 - a**2*(cx+1)**2 - 4*(1-cx**2))
print("4a^2 - a^2(cx+1)^2 - 4(1-cx^2) =", expr)

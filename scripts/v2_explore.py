import sympy as sp, numpy as np
x,y,z,c,eps=sp.symbols('x y z c epsilon',real=True)
X=(x,y,z)
rho=x**2+y**2+z**2
beta=sp.exp(-c*rho/(1-rho))
def curl(F): return sp.Matrix([sp.diff(F[2],y)-sp.diff(F[1],z), sp.diff(F[0],z)-sp.diff(F[2],x), sp.diff(F[1],x)-sp.diff(F[0],y)])
Psi = sp.Matrix([0,0,beta]) + eps*sp.Matrix([-y*z*beta, x*z*beta, 0])
u = curl(Psi); w = curl(u)
F = sum(wi**2 for wi in w)
import itertools
for cv in [3,4,6]:
  for ev in [0.1,0.3,0.5,1.0]:
    f = sp.lambdify((x,y,z), F.subs({c:cv,eps:ev}),'numpy')
    g = np.linspace(-0.999,0.999,161)
    Xg,Yg,Zg=np.meshgrid(g,g,g,indexing='ij')
    R=Xg**2+Yg**2+Zg**2
    with np.errstate(all='ignore'):
      V=np.where(R<1,f(Xg,Yg,Zg),0)
    i=np.unravel_index(np.nanargmax(V),V.shape)
    print(cv,ev,"max",np.nanmax(V),"at",g[i[0]],g[i[1]],g[i[2]],"F(0)",f(0.0,0.0,0.0))

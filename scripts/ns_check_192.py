"""NUMERICAL ONLY. Pseudo-spectral 3D NS on T^3=(R/2piZ)^3, rotational form u_t = P(u x omega) + nu Lap u,
2/3 dealiasing, RK4. Reports ||omega||_inf on the grid and |omega(0,t)| for early times."""
import numpy as np, sys, json
def run(name, u0fun, N, nu, dt, nsteps, pred_rate, M0):
    L=2*np.pi; g=np.arange(N)*L/N; g=np.where(g>np.pi,g-L,g)
    X,Y,Z=np.meshgrid(g,g,g,indexing='ij')
    k=np.fft.fftfreq(N,1/N); kz=np.fft.rfftfreq(N,1/N)
    KX,KY,KZ=np.meshgrid(k,k,kz,indexing='ij'); K2=KX**2+KY**2+KZ**2; K2i=np.where(K2==0,1,K2)
    deal=(np.abs(KX)<N/3)&(np.abs(KY)<N/3)&(np.abs(KZ)<N/3)
    F=lambda f: np.fft.rfftn(f); Fi=lambda f: np.fft.irfftn(f,s=(N,N,N))
    uh=[F(c) for c in u0fun(X,Y,Z)]
    # project initial data (should already be div-free)
    def proj(vh):
        dv=KX*vh[0]+KY*vh[1]+KZ*vh[2]
        return [vh[0]-KX*dv/K2i, vh[1]-KY*dv/K2i, vh[2]-KZ*dv/K2i]
    uh=proj(uh)
    def curl(vh): return [1j*(KY*vh[2]-KZ*vh[1]), 1j*(KZ*vh[0]-KX*vh[2]), 1j*(KX*vh[1]-KY*vh[0])]
    def rhs(vh):
        u=[Fi(c) for c in vh]; w=[Fi(c) for c in curl(vh)]
        n=[u[1]*w[2]-u[2]*w[1], u[2]*w[0]-u[0]*w[2], u[0]*w[1]-u[1]*w[0]]
        nh=proj([F(c)*deal for c in n])
        return [nh[i]-nu*K2*vh[i] for i in range(3)]
    def diag(vh):
        w=[Fi(c) for c in curl(vh)]; m=np.sqrt(w[0]**2+w[1]**2+w[2]**2)
        return float(m.max()), float(m[0,0,0])
    out=[]; tt=0.0
    for n in range(nsteps+1):
        if n%max(1,nsteps//10)==0:
            Mg,w0=diag(uh); out.append((tt,Mg,w0)); print(f"{name} t={tt:.5f} max|w|grid={Mg:.6f} |w(0)|={w0:.6f}",flush=True)
        if n==nsteps: break
        k1=rhs(uh); k2=rhs([uh[i]+dt/2*k1[i] for i in range(3)])
        k3=rhs([uh[i]+dt/2*k2[i] for i in range(3)]); k4=rhs([uh[i]+dt*k3[i] for i in range(3)])
        uh=[uh[i]+dt/6*(k1[i]+2*k2[i]+2*k3[i]+k4[i]) for i in range(3)]; tt+=dt
    t1,M1,_=out[1]; print(f"{name}: initial grid M={out[0][1]:.6f} (exact {M0}); finite-diff slope over [0,{t1:.4g}] = {(M1-out[0][1])/t1:.4f}; predicted dM/dt(0+) >= {pred_rate}")
    return out
res={}
nu=1.0
A=3.0
v1=lambda X,Y,Z: [A*(-3*np.sin(Y)-np.sin(X)*np.cos(Z)), A*3*np.sin(X), A*np.cos(X)*np.sin(Z)]
#res['V1']=run('V1(A=3,nu=1)',v1,64,nu,1e-4,200,6*A*(A-nu),6*A)
# localized field B*u1, B=10 nu, lambda=1: u1 = curl Psi, Psi=beta e_z + z beta(-y,x,0)
import sympy as sp
x,y,z=sp.symbols('x y z',real=True); r=x**2+y**2+z**2; b=sp.exp(-3*r/(1-r))
Psi=sp.Matrix([-y*z*b, x*z*b, b])
cu=lambda F: sp.Matrix([sp.diff(F[2],y)-sp.diff(F[1],z), sp.diff(F[0],z)-sp.diff(F[2],x), sp.diff(F[1],x)-sp.diff(F[0],y)])
U1=cu(Psi); fs=[sp.lambdify((x,y,z),c,'numpy') for c in U1]
B=10*nu
def v2(X,Y,Z):
    R=X**2+Y**2+Z**2; m=R<1
    out=[]
    for f in fs:
        a=np.zeros_like(X)
        with np.errstate(all='ignore'): a[m]=B*f(X[m],Y[m],Z[m])
        out.append(a)
    return out
res['V2loc']=run('V2-localized(B=10,lambda=1,nu=1)',v2,int(sys.argv[1]) if len(sys.argv)>1 else 128,nu,2e-6,20,24*B*(B-5*nu),12*B)
json.dump(res,open('ns_check_results_192.json','w'),indent=1)

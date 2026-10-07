"""Numeric check of the exact formal statement in Miquel/Main.lean (frame of Miquel/Coeffs.lean).
Random triangles A,B,C; F=A+n(B-A), E=A+t(C-A), D=B+u(C-B) (n,t,u arbitrary reals, extended sides
allowed). M is the radical-axis point (rpx, rpy) used in the proof; check |M-O_i| = r_i for all three
circumcircles. Negative control: F itself (on circles 1 and 2) is generally off circle 3."""
import random
def cc(P,R,S):
    (p0,p1),(r0,r1),(s0,s1)=P,R,S
    d=-p0*r1+p0*s1+p1*r0-p1*s0-r0*s1+r1*s0
    nP=p0*p0+p1*p1;nR=r0*r0+r1*r1;nS=s0*s0+s1*s1
    X=-((nR-nP)*(s1-p1)-(nS-nP)*(r1-p1));Y=-((r0-p0)*(nS-nP)-(s0-p0)*(nR-nP))
    o=(X/(2*d),Y/(2*d)); return o, ((p0-o[0])**2+(p1-o[1])**2)**.5
def dist(a,b): return ((a[0]-b[0])**2+(a[1]-b[1])**2)**.5
random.seed(7); worst=0; negmin=1e9
for _ in range(20000):
    A=(random.uniform(-3,3),random.uniform(-3,3));B=(random.uniform(-3,3),random.uniform(-3,3));C=(random.uniform(-3,3),random.uniform(-3,3))
    n,t,u=[random.uniform(-2,3) for _ in range(3)]
    F=(A[0]+n*(B[0]-A[0]),A[1]+n*(B[1]-A[1]));E=(A[0]+t*(C[0]-A[0]),A[1]+t*(C[1]-A[1]));D=(B[0]+u*(C[0]-B[0]),B[1]+u*(C[1]-B[1]))
    try:
        (o1,r1),(o2,r2),(o3,r3)=cc(A,E,F),cc(B,F,D),cc(C,D,E)
    except ZeroDivisionError: continue
    # second intersection of circles 1,2 through F: reflect F across the line of centres
    vx,vy=o2[0]-o1[0],o2[1]-o1[1]; L=vx*vx+vy*vy
    k=((F[0]-o1[0])*vx+(F[1]-o1[1])*vy)/L
    foot=(o1[0]+k*vx,o1[1]+k*vy); M=(2*foot[0]-F[0],2*foot[1]-F[1])
    sc=dist(A,B)+dist(B,C)+dist(C,A)
    if max(r1,r2,r3)>1e3*sc: continue
    worst=max(worst,abs(dist(M,o1)-r1)/sc,abs(dist(M,o2)-r2)/sc,abs(dist(M,o3)-r3)/sc)
    negmin=min(negmin,abs(dist(F,o3)-r3)/sc) if abs(dist(F,o3)-r3)/sc>0 else negmin
print("worst relative residual of Miquel point on all 3 circles:",worst)
print("negative control (F on circle 3?) median-ish lower bound:",negmin)
# concrete instance used in Lean: A=0,B=4,C=1+3i, midpoints
A,B,C=(0,0),(4,0),(1,3);D,E,F=(2.5,1.5),(0.5,1.5),(2,0)
o3,r3=cc(C,D,E); print("Lean negative control |F-O3|-r3 =",dist(F,o3)-r3)

// The code in this file proves the claims made in the first  paragraph of Proposition 8.1
// Parts of the code were provided to us by Petar Orlić from a different unpublished project. 


////////////////////////////////////////////////////////////////////////////////////////
//We will chech for all elliptic curves corresponding to degree 3 points on X0(30), none have an isogeny of degree 4, so do not lift to a degree 3 point on X0(60)
//////////////////////////////////////////////////////////////////////////////////////////
Qx<x>:=PolynomialRing(Rationals());
X:=SmallModularCurve(30);
cusps:=&cat[CuspPlaces(X,30,d) : d in Divisors(30)];

assert &and[Degree(P) eq 1 : P in cusps];
assert #NonCuspidalQRationalPoints(X,30) eq 0;

Y:=HyperellipticCurve(3*x^7+19*x^6+60*x^5+110*x^4+121*x^3+79*x^2+28*x+4, -x^4-x^3-x^2);

tf,phi:=IsIsomorphic(X,Y);
assert tf;
cusps:={Pushforward(phi,c) : c in cusps};
ptsY:= [ Y![1 , 1 , 0], Y![1 , 0 , 0], Y![-2 , 4 , 1], Y![-2 , 8 , 1], Y![-1 , 0 , 1], Y![0 , -2 , 1], Y![-1 , 1 , 1], Y![0 , 2 , 1]];
assert cusps eq {Place(p) : p in ptsY};

p0:=ptsY[1];

J:=Jacobian(Y);
ptsJ:=[ p-p0 : p in ptsY   ];
J7:=BaseChange(J,GF(7));
B,mu:=AbelianGroup(J7);

A:=FreeAbelianGroup(8);
eps:=hom<A->B | [ (J7!Q)@@mu : Q in ptsJ  ] >;
C:=Image(eps);

Q1:=ptsJ[4]; //24
Q2:=ptsJ[7]; //4
Q3:=3*ptsJ[5]; //2
mu1:=(J7!Q1)@@mu;
mu2:=(J7!Q2)@@mu;
mu3:=(J7!Q3)@@mu;

cuspGp:=AbelianGroup([24,4,2]);
delta:=hom<cuspGp->C | [mu1,mu2,mu3]>;
assert #Kernel(delta) eq 1; //So Q1,Q2,Q3 generate the torsion
assert Image(delta) eq C;

cuspGpElts:={a*Q1+b*Q2+c*Q3 : a in [0..23], b in [0..3], c in [0..1]};
assert #cuspGpElts eq 24*4*2;

D1:=Place(ptsY[4])-Place(ptsY[1]);
D2:=Place(ptsY[7])-Place(ptsY[1]);
D3:=2*Place(ptsY[5])-2*Place(ptsY[1]);

infdiv:=3*Place(ptsY[1]);

deg3:=[a*D1+b*D2+c*D3+infdiv : a in [0..23], b in [0..3], c in [0..1]];

assert #deg3 eq 192;
assert &and[Degree(D) eq 3 : D in deg3];
assert &and[Dimension(RiemannRochSpace(D)) in [1,2] : D in deg3];//The divisors for which RR spaces have dimension 2 are a degree 2 rational divisor + a rational point 
deg3:=[ D : D in deg3 | Dimension(RiemannRochSpace(D)) eq 1];
assert #deg3 eq 184;

deg3new:=[];
for D in deg3 do
L,mu:=RiemannRochSpace(D);
assert Dimension(L) eq 1;
D1:=D+Divisor(mu(L.1));
assert IsEffective(D1);
decomp:=Decomposition(D1);
if #decomp eq 1 and decomp[1,2] eq 1 then
Append(~deg3new,decomp[1,1]);
end if;
end for;

assert #deg3new eq 48;
real:=0;
complex:=0;

for D in deg3new do
K:=ResidueClassField(D);
assert IsNumberField(K);
assert Degree(K) eq 3;
if IsTotallyReal(K) eq true then
    real:=real+1;
else complex:=complex+1;
end if;
end for;

assert real eq 16;
assert complex eq 32;

for a in deg3new do
	K<w>:=ResidueClassField(a);
	P:=RepresentativePoint(deg3new[1]);
	XK:=ChangeRing(X,K);
	Q:=Points(XK,w)[1];
	j:=jInvariant(Q,30);
	E:=EllipticCurveFromjInvariant(j);
	ck:=Degree(Factorization(DivisionPolynomial(E,4) div DivisionPolynomial(E,2))[1,1]); //If E had an isogeny of degree 4, then this polynomial would have a linear factor.
	//ck;
	assert ck ge 2;
end for;

//Complete: no degree 3 points noncuspidal points on X0(60).







////////////////////////////////////////////////////////////////////////////////
//We will chech for all elliptic curves corresponding to degree 3 points on X0(35), none have an isogeny of degree 2, so do not lift to a degree 3 point on X0(70). See the case N=30 for a bit more explanation of the code. 
////////////////////////////////////////////////////////////////////////////////
Qx<x>:=PolynomialRing(Rationals());
X:=SmallModularCurve(35);
cusps:=&cat[CuspPlaces(X,35,d) : d in Divisors(35)];
assert &and[Degree(P) eq 1 : P in cusps];
assert #NonCuspidalQRationalPoints(X,35) eq 0;

Y:=HyperellipticCurve( -x^7 - 2*x^6 - x^5 -3*x^4 + x^3 - 2*x^2 + x, -x^4 - x^2 - 1);

 Qx<x>:=PolynomialRing(Rationals());
 X:=SmallModularCurve(35);
 cusps:=&cat[CuspPlaces(X,35,d) : d in Divisors(35)];
 assert &and[Degree(P) eq 1 : P in cusps];
 assert #NonCuspidalQRationalPoints(X,35) eq 0;

 Y:=HyperellipticCurve( -x^7 - 2*x^6 - x^5 -3*x^4 + x^3 - 2*x^2 + x, -x^4 - x\
^2 - 1);
 ptsY:= [ Y![1 , 0 , 0], Y![1 , 1 , 0], Y![0 , 0 , 1], Y![0 , 1 , 1]];
 ptsX:= [ X![1 , 0 , 0], X![1 , 1 , 0], X![0 , 0 , 1], X![0 , 1 , 1]];
 tf,phi:=IsIsomorphic(X,Y);
 assert tf;
 cuspsY:={Pushforward(phi,c) : c in cusps};
 assert cuspsY eq {Place(p) : p in ptsY};
 J:=Jacobian(Y);
 p0:=ptsY[1];
 ptsJ:=[ p-p0 : p in ptsY   ];
 
J11:=BaseChange(J,GF(11));
B,mu:=AbelianGroup(J3);
A:=FreeAbelianGroup(4);
eps:=hom<A->B | [ (J3!Q)@@mu : Q in ptsJ  ] >;
C:=Image(eps);

Q1:=ptsJ[2];
Q2:=ptsJ[3];
set:={};
for i:=1 to 24 do for j:=1 to 2 do set:=set join{i*Q1+j*Q2}; end for; end for;
assert #set eq 48;

cuspGpElts:={a*Q1+b*Q2 : a in [0..23], b in [0..1]};
assert #cuspGpElts eq 48;

D1:=Place(ptsY[2])-Place(ptsY[1]);
D2:=Place(ptsY[3])-Place(ptsY[1]);
 
 
infdiv:=3*Place(ptsY[1]);

deg3:=[a*D1+b*D2+infdiv : a in [0..23], b in [0..1]];

assert #deg3 eq 48;
assert &and[Degree(D) eq 3 : D in deg3];

assert &and[Dimension(RiemannRochSpace(D)) in [1,2] : D in deg3];

deg3:=[ D : D in deg3 | Dimension(RiemannRochSpace(D)) eq 1];

assert #deg3 eq 44;

deg3new:=[];
for D in deg3 do
L,mu:=RiemannRochSpace(D);
assert Dimension(L) eq 1;
D1:=D+Divisor(mu(L.1));
assert IsEffective(D1);
decomp:=Decomposition(D1);
if #decomp eq 1 and decomp[1,2] eq 1 then
Append(~deg3new,decomp[1,1]);
end if;
end for;

assert #deg3new eq 32;



for a in deg3new do
	K<w>:=ResidueClassField(a);
	P:=RepresentativePoint(deg3new[1]);
	XK:=ChangeRing(X,K);
	Q:=Points(XK,w)[1];
	j:=jInvariant(Q,35);
	E:=EllipticCurveFromjInvariant(j);
	assert #TwoTorsionSubgroup(E) eq 1;//So there are no isogenies of degree 2
end for;

// no deg 3 points on X0(70).












//////////////////////////////////////////////////////////////
//We will chech for all elliptic curves corresponding to degree 3 points on X0(40), none have an isogeny of degree 16, so do not lift to a degree 3 point on X0(80). See the case N=30 for a bit more explanation of the code. 
/////////////////////////////////////////////////////////////


X_0(40):

Qx<x>:=PolynomialRing(Rationals());

X:=SmallModularCurve(40);

cusps:=&cat[CuspPlaces(X,40,d) : d in Divisors(40)];

assert &and[Degree(P) eq 1 : P in cusps];
assert #NonCuspidalQRationalPoints(X,40) eq 0;

Y:=HyperellipticCurve(2*x^6-x^4+2*x^2, -x^4-1);

tf,phi:=IsIsomorphic(X,Y);
assert tf;

cusps:={Pushforward(phi,c) : c in cusps};

ptsY:= [ Y![1 , 1 , 0], Y![1 , 0 , 0], Y![0 , 0 , 1], Y![0 , 1 , 1], Y![1 , 3 , 1], Y![1 , -1 , 1], Y![-1 , 3 , 1], Y![-1 , -1 , 1]];
assert cusps eq {Place(p) : p in ptsY};

p0:=ptsY[1];

J:=Jacobian(Y);
ptsJ:=[ p-p0 : p in ptsY   ];

J3:=BaseChange(J,GF(3));
B,mu:=AbelianGroup(J3);
A:=FreeAbelianGroup(8);
eps:=hom<A->B | [ (J3!Q)@@mu : Q in ptsJ  ] >;
C:=Image(eps);

Q1:=ptsJ[2];
Q2:=ptsJ[5];
mu1:=(J3!Q1)@@mu;
mu2:=(J3!Q2)@@mu;

cuspGp:=AbelianGroup([12,12]);
delta:=hom<cuspGp->C | [mu1,mu2]>;
assert #Kernel(delta) eq 1;
assert Image(delta) eq C;

cuspGpElts:={a*Q1+b*Q2 : a in [0..11], b in [0..11]};
assert #cuspGpElts eq 144;

D1:=Place(ptsY[2])-Place(ptsY[1]);
D2:=Place(ptsY[5])-Place(ptsY[1]);

infdiv:=3*Place(ptsY[1]);

deg3:=[a*D1+b*D2+infdiv : a in [0..11], b in [0..11]];

assert #deg3 eq 144;
assert &and[Degree(D) eq 3 : D in deg3];

assert &and[Dimension(RiemannRochSpace(D)) in [1,2] : D in deg3];

deg3:=[ D : D in deg3 | Dimension(RiemannRochSpace(D)) eq 1];

assert #deg3 eq 136;

deg3new:=[];
for D in deg3 do
L,mu:=RiemannRochSpace(D);
assert Dimension(L) eq 1;
D1:=D+Divisor(mu(L.1));
assert IsEffective(D1);
decomp:=Decomposition(D1);
if #decomp eq 1 and decomp[1,2] eq 1 then
Append(~deg3new,decomp[1,1]);
end if;
end for;

assert #deg3new eq 32;

for D in deg3new do
K:=ResidueClassField(D);
assert IsNumberField(K);
assert Degree(K) eq 3;
assert IsTotallyReal(K) eq false;
assert Discriminant(K) lt 0;
end for;


for a in deg3new do
	K<w>:=ResidueClassField(a);
	P:=RepresentativePoint(deg3new[1]);
	XK:=ChangeRing(X,K);
	Q:=Points(XK,w)[1];
	j:=jInvariant(Q,40);
	E:=EllipticCurveFromjInvariant(j);
	_<y>:=PolynomialRing(K);
	ck:=Degree(Factorization(Evaluate(ClassicalModularPolynomial(16),[j,y]))[1,1]);// so there are no isogenies of degree 16
	//ck;
	assert ck ge 2;
end for;


// no deg 3 points









//////////////////////////////////////////////////////////////////////////////////////
//We will chech for all elliptic curves corresponding to degree 3 points on X0(47), none have an isogeny of degree 2, so do not lift to a degree 3 point on X0(94). See the case N=30 for a bit more explanation of the code. 
////////////////////////////////////////////////////////////////////////////////////

//This fucntion works only for prime level, It computes all the divisor classes in Pic^d X_0(N) and returns their dimensions, and the unique deg d effective divisors in those classes with dimension 1

function riemann_roch_spaces_X_0(N,d)
    assert IsPrime(N);
    tors_order := Numerator((N-1)/12);
    X:=SimplifiedModel(ModularCurveQuotient(N,[]));
    ptsX:=Points(X : Bound:=10000);
    P:=Divisor(ptsX[1]);
    Q:=Divisor(ptsX[2]);
    assert IsPrincipal(tors_order*(P-Q));
    dimensions := [];
    unique_divisors := [];
    n := tors_order div 2;
    for a in [-n + ((tors_order+1) mod 2)..n] do
       dimension := [a,Dimension(P+Q+(d-2)*Q + a*(P-Q))];
       Append(~dimensions,dimension);
       if dimension[2] eq 1 then;
           V,phi := RiemannRochSpace(P+Q+(d-2)*Q + a*(P-Q));
           Ds := [D : D in Support(Divisor(phi(V.1))) | Degree(D) eq d];
           if #Ds ne 0 then
               Append(~unique_divisors,Ds[1]);
           end if;
       end if;
    end for;
    return dimensions,unique_divisors;
end function;



p:=47;
dims,divs := riemann_roch_spaces_X_0(p,2);
print [dim : dim in dims | dim[2] ne 0];
/*
[
    [ -1, 1 ],
    [ 0, 2 ],
    [ 1, 1 ]
]
*/
divs;
//[] As expected, no exceptional points

dims,divs := riemann_roch_spaces_X_0(p,3);
/*
[
    [ -8, 1 ],
    [ -1, 1 ],
    [ 0, 2 ],
    [ 1, 2 ],
    [ 2, 1 ],
    [ 9, 1 ]
]
Note: the classes with dimension 2 will not contain irreducible divisors.
*/
fields := [ResidueClassField(D) : D in divs];
print [dim : dim in dims | dim[2] ne 0],[<Discriminant(K),DefiningPolynomial(K)> : K in fields];
/*
[
    <-883, $.1^3 - 5/2*$.1^2 + 5/2*$.1 + 1/2>,
    <-883, $.1^3 - 5/2*$.1^2 + 5/2*$.1 + 1/2>
]
So we have 3 deg 3 points on X_0(47)
*/
K:=fields[1];	
XK:=ChangeRing(SmallModularCurve(47),K);
pts:=Points(XK:Bound:=10);
j1:=jInvariant(pts[3],47);
E1:=EllipticCurveFromjInvariant(j1);
j2:=jInvariant(pts[4],47);
E2:=EllipticCurveFromjInvariant(j1);
assert j1 ne j2; //These are the only 2 deg3 j-invariants on X0(47) 
assert #TwoTorsionSubgroup(E2) eq 1;
assert #TwoTorsionSubgroup(E2) eq 1;
//done, so neither of these points lift to X0(94)


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//We will chech for all elliptic curves corresponding to degree 3 points on X0(48), none have an isogeny of degree 32, so do not lift to a degree 3 point on X0(96).cSimilarly, no points have a degree 9 isogeny, so do not lift to degree 2 points on X0(144). See the case N=30 for a bit more explanation of the code. 
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

Qx<x>:=PolynomialRing(Rationals());
X:=SmallModularCurve(48);
cusps:=&cat[CuspPlaces(X,48,d) : d in Divisors(48)];
Y:=HyperellipticCurve(x^8+14*x^4+1);
tf,phi:=IsIsomorphic(X,Y);
assert tf;
cusps:=&cat[CuspPlaces(X,48,d) : d in Divisors(48)];
assert &and[Degree(P) eq 1 or Degree(P) eq 2 : P in cusps];
assert #NonCuspidalQRationalPoints(X,48) eq 0;
ptsY:= [ Y![1 , 1 , 0], Y![1 , -1 , 0], Y![1 , 4 , 1], Y![-1 , 4 , 1] , Y![1 , -4 , 1], Y![-1 , -4 , 1], Y![0 , 1 , 1], Y![0 , -1 , 1]];
p0:=ptsY[1];
J:=Jacobian(Y);
ptsJ:=[ p-p0 : p in ptsY   ];
J5:=BaseChange(J,GF(5));
B,mu:=AbelianGroup(J5);
A:=FreeAbelianGroup(8);
eps:=hom<A->B | [ (J5!Q)@@mu : Q in ptsJ  ] >;
C:=Image(eps);
Q1:=ptsJ[3];
mu1:=(J5!Q1)@@mu;
Q2:=ptsJ[2];
mu2:=(J5!Q2)@@mu;
Q3:=ptsJ[7];
mu3:=(J5!Q3)@@mu;
cuspGp:=AbelianGroup([8,4,4]);
delta:=hom<cuspGp->C | [mu1,mu2,mu3]>;
assert #Kernel(delta) eq 1;
assert Image(delta) eq C;
cuspGpElts:={a*Q1+b*Q2+c*Q3 : a in [0..7], b in [0..3], c in [0..3]};
assert #cuspGpElts eq 128;
D1:=Place(ptsY[3])-Place(ptsY[1]);
D2:=Place(ptsY[2])-Place(ptsY[1]);
D3:=Place(ptsY[7])-Place(ptsY[1]);
infdiv:=3*Place(ptsY[1]);
deg3:=[a*D1+b*D2+c*D3+infdiv : a in [0..7], b in [0..3], c in [0..3]];
assert #deg3 eq 128;
assert &and[Degree(D) eq 3 : D in deg3];
assert &and[Dimension(RiemannRochSpace(D)) in [1,2] : D in deg3];
deg3:=[ D : D in deg3 | Dimension(RiemannRochSpace(D)) eq 1];
assert #deg3 eq 120;
deg3new:=[];
for D in deg3 do
L,mu:=RiemannRochSpace(D);
assert Dimension(L) eq 1;
D1:=D+Divisor(mu(L.1));
assert IsEffective(D1);
decomp:=Decomposition(D1);
if #decomp eq 1 and decomp[1,2] eq 1 then
Append(~deg3new,decomp[1,1]);
end if;
end for;

assert #deg3new eq 16;

for D in deg3new do
K:=ResidueClassField(D);
assert IsNumberField(K);
assert Degree(K) eq 3;
assert IsTotallyReal(K) eq false;
assert Discriminant(K) lt 0;
end for;



for a in deg3new do
	K<w>:=ResidueClassField(a);
	P:=RepresentativePoint(deg3new[1]);
	XK:=ChangeRing(X,K);
	Q:=Points(XK,w)[1];
	j:=jInvariant(Q,48);
	E:=EllipticCurveFromjInvariant(j);
	_<y>:=PolynomialRing(K);
	ck:=Degree(Factorization(Evaluate(ClassicalModularPolynomial(32),[j,y]))[1,1]); // we check that no curve has an isogeny of degree 32
	//ck;
	assert ck ge 2;
	ck:=Degree(Factorization(Evaluate(ClassicalModularPolynomial(9),[j,y]))[1,1]); // we check that no curve has an isogeny of degree 9
	//ck;
	assert ck ge 2;
	
end for;
//Complete: no degree 3 points on X_0(96) or X_0(144).

 





















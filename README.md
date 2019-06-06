###################################################################################
###### Quick guide on the functionality of the Magma package riemann-surfaces #####
###### 				Christian Neurohr 2019			      #####
###################################################################################

Important intrinsics:
	- RiemannSurface (type: RieSrf)
	- BigPeriodMatrix
	- SmallPeriodMatrix
	- MonodromyRepresentation
	- FundamentalGroup
	- HomologyBasis
	- InfinitePoints
	- Genus
	- Precision
	- DefiningPolynomial
	- ComplexPolynomialn
	- Embedding
	- HomogeneousPolynomial
	- FunctionField
	- BasePoint
	- Degree
	- BranchPoints
	- DiscriminantPoints
	- IsSuperelliptic
	- HolomorphicDifferentials
	- BaseRing
	- SingularPoints
	- FundamentalGroup
	- RamificationPoints
	- RandomRiemannSurface

Numerical integration routines:
	- TanhSinhIntegrationPoints (Double-exponential)
	- GaussLegendreIntegrationPoints
	- ClenshawCurtisIntegrationPoints
	- GaussJacobiIntegrationPoints
	- DiscreteFourierTransform

Abel-Jacobi map, Points & Divisors:
	- AbelJacobi
	- Point (type: RieSrfPt)
	- RandomPoint
	- Coordinates
	- IsFinite
	- RamificationIndex
	- Representation
	- PointsOverDiscriminantPoint
	- Divisor (type: DivRieSrfElt)
	- ZeroDivisor
	- RandomDivisor
	- Support
	- Degree
	- RiemannSurface

/* Examples from my PhD-thesis */

Qxy<x,y> := PolynomialRing(Rationals(),2);

f1 := x^9 + 2*x^6*y^2 + x^2 + y^6 + 2*y^4;
f2 := 15*x^5*y^5 + 44*x^4*y + 24*x^3*y^3 + 15*x*y^4 - 49;
// f3 left out here
f4 := x^6*y^6 + x^3 + y^2 + 1;
f5 := -x^4 - x^3 + 2*x^2 - 2*x + y^3 - 4;
f6 := 23*x^6*y + x*y^5 - 100*y^2 - 10000*y + 1;
f7 := -x^7 + 2*x^3*y + y^3;

q1 := x^3*y + x^3 + x^2*y^2 + 3*x^2*y + x^2 - 4*x*y^3 - 3*x*y^2 - 3*x*y - 4*x + 2*y^4 + 3*y^2 + 2;
q2 := x^3 + x^2 + x*y^3 - x*y^2 + y^2 - y;
q3 := x^4 + 2*x^3*y + 2*x^3 - 4*x^2*y^2 + 2*x^2*y - 4*x^2 - x*y^3 - x + 2*y^4 - 3*y^3 + 5*y^2 - 3*y + 2;
q4 := x^3 + x^2*y^2 + x^2*y + x*y^3 + x*y^2 + x*y + x + y^3 + y^2;
q5 := x^3 + x^2*y^2 + x*y^3 - x*y^2 - 2*x - y^2 - 1;
q6 := x^3 + x^2*y + x^2 - x*y^3 + x*y^2 + x - y^2 + y;
q7 := x^3 + x^2*y + x^2 + x*y^3 - 3*x*y^2 - 4*x - y^4 + 2*y^3 + 2;
q8 := x^3 + x^2*y^2 + x^2 + x*y^3 + x*y + y^3 + y;
q9 := x^3 + x^2*y + x^2 + x*y^3 + x*y + y^3 + y^2 + y;

function fk(k) return x^k*y^2 + (x+y)^(k-1) + 1; end function;

/* Some other examples */

g1 := -x^6 - 2*x^3*y + y^3 - y^2 + 1;
g2 := -4*x^4 - 5*x^3*y + x^3 + 2*x^2*y^2 - 5*x^2*y + 3*x^2 + 3*x*y^3 + x*y - 5*x - 8*y^3 - 3;
g3 := -2*x^6 + 7*x^5 - 7*x^4 + 5*x^3 + 4*x^2 + 6*x + y^5 - 3;
g4 := x^3*y^4 + 2*x^3*y + 4*x^2*y^2 - 1;

/* Random polynomials defined over a random number field; degrees can also be chosen higher here */

g5 := RandomRiemannSurface(Random([2..4]),Random([2..4]):NFDeg:=Random([1..5])); 
g6 := RandomRiemannSurface(Random([2..4]),Random([2..4]):NFDeg:=Random([1..5])); 

F := <f1,f2,f4,f5,f6,f7,q1,q2,q3,q4,q5,q6,q7,q8,q9,fk(Random([2..10])),g1,g2,g3,g4,g5,g6>;

/* Printing */
SetVerbose("RS",2);

/* Choose a random example */
f := F[Random([1..#F])];

/* Desired precision in decimal digits */
Prec := Random([30,100]); // Precision can be higher than 100

/* Different integration method: Gauss-Legendre (GL), Clenshaw-Curtis (CC), Double-exponential (DE) + Mixed (GL+DE),
 Default method is Mixed */
IntMethod := Random(["GL","CC","DE","Mixed"]); 

/* Defined over \Q ? */
if BaseRing(Parent(f)) eq Rationals() then
	time MR := MonodromyRepresentation(f);
	time Cycles, IntMat := HomologyBasis([Gamma`Permutation : Gamma in MR]);
	time X := RiemannSurface(f:Precision:=Prec,IntMethod:=IntMethod); // define a Riemann surface, computes period matrices, sets up Abel-Jacobi map
	HomologyGroup(X);
	FundamentalGroup(X);
	BigPeriodMatrix(X);
	SmallPeriodMatrix(X);	
else
	P := Random(InfinitePlaces(BaseRing(Parent(f)))); // choose a complex embedding
	time MR := MonodromyRepresentation(f,P);
	time Cycles, IntMat := HomologyBasis([Gamma`Permutation : Gamma in MR]);
	time X := RiemannSurface(f,P:Precision:=Prec,IntMethod:=IntMethod);
	FundamentalGroup(X);
	HomologyGroup(X);
	BigPeriodMatrix(X);
	SmallPeriodMatrix(X);
end if;

/* Compute the Abel-Jacobi map of some random divisor */
for k in [1..10] do
	Reduction := Random(["Real","Complex"]);
	Method := Random(["Swap","Direct"]);
	Pt := RandomPoint(X);
	AJPt := AbelJacobi(P);
	Div := RandomDivisor(X,k);
	AJDiv := AbelJacobi(Div:Method:=Method,Reduction:=Reduction);
end for;

///////////////////////////////////////////////////////////////////////////////
/// ################# More details on the Abel-Jacobi map ################# ///
///////////////////////////////////////////////////////////////////////////////

/* Define Riemann surface */
	Qxy<x,y> := PolynomialRing(Rationals(),2);
	f := x^3 + x^2 + x*y^3 - x*y^2 + y^2 - y;
	X := RiemannSurface(f:Precision:=50);
	C<I> := X`ComplexFields[3];

/* First option: compute Abel-Jacobi map from the base point to a regular point P = <x_P,y_P>, say */
	X`BasePoint; // Base point
	x_P := C!5; 
	Y_P := X`Fiber(x_P); 
	y_P := Y_P[Random([1..X`Degree[1]])];
	P := X![x_P,y_P];
	v1 := AbelJacobi(P); // should be the same as
	v2 := AbelJacobi(X`BasePoint,P);
	assert v1 eq v2;
/* Alternatively, enter the point as P = <x_P,s>, where s in [1..m] is an integer that indexes the sheet */
	Q := X!<x_P,Random([1..X`Degree[1]])>;
	v3 := AbelJacobi(Q);

/* Now look at points lying over discriminant points */
	DP := X`DiscriminantPoints;
	x1 := DP[1]; x2 := DP[2];
	y1 := X`Fiber(x1)[1]; y2 := X`Fiber(x2)[1];
	Q1 := X![x1,y1]; Q2 := X![x2,y2];
	v := AbelJacobi(Q1,Q2);

/* Finally, for divisors */
	Div1 := 2*X![x_P,y_P] - 2*X!<x_P,3> + 4*Q1 + Q2 + 10*X!<Infinity(),3>;
	v1 := AbelJacobi(Div1);
	Div2 := RandomDivisor(X,10);
	v2 := AbelJacobi(Div2);

/* Computing the Abel-Jacobi map of ramification points */
	RP := RamificationPoints(X);
	v1 := AbelJacobi(RP[1]);

	/* Here: (0,0) is a singularity of the affine curve, and numerical integration does not work in this instance;
	should show a message: "Warning! Significant digits for integral to discriminant point: _ " */
	RP[2] = (0.0000000000, {@ 1, 3 @}) */
	v2 := AbelJacobi(RP[2]);
	
	/* Solution: Use Function Field! */
	FF<x,y> := FunctionField(X);
	Px := Zeros(x);
	AbelJacobi(X,Px[1]);
	AbelJacobi(X,Px[2]);
	AbelJacobi(X,Px[1]+Px[2]);


/* Another example: /*
	X := RiemannSurface(g4:Precision:=50);

	/* Some interesting y-infinite points */
	DP := X`DiscriminantPoints;
	x1 := DP[8];
	x2 := DP[9];
	x3 := DP[10];
	Points := < <x1,Infinity(),1>, <x2,Infinity(),1>, <x3,Infinity(),1> >;
	D := Divisor(Points,X);
	v1 := AbelJacobi(D,X);

	/* Singularity at (0,0) with ramification index 3; see X`ClosedChains */
	v2 := AbelJacobi(X!<0,1>);
	w2 := AbelJacobi(X!<0,2>);
	assert v2 eq w2;

	// Integrate infinity with ramification index 3 // see X`InfiniteChain
	v3 := AbelJacobi(<Infinity(),2>,X);
	w3 := AbelJacobi(<Infinity(),3>,X);
	assert v3 eq w3;


////////////////////////////////////////////////
// Reproducing the timings from my PhD-thesis //
////////////////////////////////////////////////

	Precisions := [50,100,200];
	Polynomials := [ fk(k) : k in [2..10] ] cat [q1,q2,q3,q4,q5,q6,q7,q8,q9];
	Times := [];
	for f in Polynomials do
		for Prec in Precisions do
			print "f:",f;
			print "Prec:",Prec;
			t := Cputime();
			time X := RiemannSurface(f:Precision:=Prec,IntMethod:="Mixed");
			Append(~Times,<f,Prec,Cputime()-t>);
		end for;
	end for;
	Times;















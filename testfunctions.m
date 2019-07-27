import "integration.m": SE_AJM_InftyPoints;
import "homology.m": SymplecticTransformation;

/* Test functions for Abel-Jacobi map */
intrinsic AJM_Test(X::RieSrf) -> RngIntElt
{ Strong test for the Abel-Jacobi map of superelliptic curves }
	C<I> := X`ComplexFields[3];
	m := X`Degree[1];
	V := AbelJacobi(m*(Random(X`CriticalPoints)-Random(X`CriticalPoints)):Method:="Swap");
	return V;
end intrinsic;
intrinsic AJM_Test_1( X::RieSrf : Ht := 10^5 ) -> RngIntElt
{ Weak test for Abel-Jacobi map of superelliptic curves }
	m := X`Degree[1];
	n := X`Degree[2];
	C<I> := X`ComplexFields[3];
	x1 := C!Random([-Ht..Ht])/Random([1..Ht]) + I*C!Random([-Ht..Ht])/Random([1..Ht]);
	x2 := C!Random([-Ht..Ht])/Random([1..Ht]) + I*C!Random([-Ht..Ht])/Random([1..Ht]);
	F1 := X`Fiber(x1);
	F2 := X`Fiber(x2);
	S1 := []; S2 := [];
	for j in [1..m] do
		Append(~S1,X![x1,F1[j]]);
		Append(~S2,X![x2,F2[j]]);
	end for;
	D := &+S1 - &+S2;
	return AbelJacobi(D);
end intrinsic;
intrinsic AJM_Test_2( X::RieSrf : Ht := 10^5 ) -> RngIntElt
{ Strong test: Abel-Jacobi map along D=div((y-y1)/(y-y2)) must be zero }
	m := X`Degree[1];
	n := X`Degree[2];
	f := X`ComplexDefPol;
	C<I> := BaseRing(Parent(f));
	y1 := C!Random([-Ht..Ht])/Random([1..Ht]) + I*C!Random([-Ht..Ht])/Random([1..Ht]);
	y2 := C!Random([-Ht..Ht])/Random([1..Ht]) + I*C!Random([-Ht..Ht])/Random([1..Ht]);
	if X`IsSuperelliptic then
		g1 := f - y1^m; 
		g2 := f - y2^m;
	else
		g1 := UnivariatePolynomial(Evaluate(f,[Parent(f).1,y1]));
		g2 := UnivariatePolynomial(Evaluate(f,[Parent(f).1,y2]));
	end if;
	F1 := RootsNonExact(g1);
	F2 := RootsNonExact(g2);
	assert #F1 eq #F2;
	S1 := []; S2 := [];
	for j in [1..n] do
		Append(~S1,X![F1[j],y1]);
		Append(~S2,X![F2[j],y2]);
	end for;
	D := &+S1 - &+S2;
	return AbelJacobi(D);
end intrinsic;
intrinsic AJM_Test_3( X::RieSrf : Ht := 10^5 ) -> RngIntElt
{ Strong test: Abel-Jacobi map along D=div(x-x0) must be zero }
	m := X`Degree[1];
	n := X`Degree[2];
	f := X`ComplexDefPol;
	C<I> := BaseRing(Parent(f));
	x0 := C!Random([-Ht..Ht])/Random([1..Ht]) + I*C!Random([-Ht..Ht])/Random([1..Ht]);
	F := X`Fiber(x0);
	S := [ X![x0,F[j]] : j in [1..m] ];
	if X`IsSuperelliptic then
		D := &+S - Round(m/X`Degree[3])*&+X`InfinitePoints;
	else
		D := &+S - &+[ X!<Infinity(),s> : s in [1..m]];
	end if;
	return AbelJacobi(D); 
end intrinsic;


intrinsic TestAll() -> .
{ Test all of the functions. }
	SetVerbose("RS",2);
	Qxy<x,y> := PolynomialRing(RationalsAsNumberField(),2);
	f1 := x^9 + 2*x^6*y^2 + x^2 + y^6 + 2*y^4;
	f2 := 15*x^5*y^5 + 44*x^4*y + 24*x^3*y^3 + 15*x*y^4 - 49;
	f4 := x^6*y^6 + x^3 + y^2 + 1;
	f5 := -x^4 - x^3 + 2*x^2 - 2*x + y^3 - 4;
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

	// Some other examples
	g1 := -x^6 - 2*x^3*y + y^3 - y^2 + 1;
	g2 := -4*x^4 - 5*x^3*y + x^3 + 2*x^2*y^2 - 5*x^2*y + 3*x^2 + 3*x*y^3 + x*y - 5*x - 8*y^3 - 3;
	g3 := -2*x^6 + 7*x^5 - 7*x^4 + 5*x^3 + 4*x^2 + 6*x + y^5 - 3;
	g4 := x^3*y^4 + 2*x^3*y + 4*x^2*y^2 - 1;
	g5 := RandomRiemannSurface(Random([2..4]),Random([2..4]):NFDeg:=Random([1..5])); // Random polynomials defined over a random number field
	g6 := RandomRiemannSurface(Random([2..4]),Random([2..4]):NFDeg:=Random([1..5])); // Degrees can also be chosen higher here
	g7 := RandomRiemannSurface(Random([2..4]),Random([2..4]):NFDeg:=Random([1..5]));
	g8 := RandomRiemannSurface(Random([2..4]),Random([2..4]):NFDeg:=Random([1..5]));

	F := <f1,f2,f4,f5,f7,q1,q2,q3,q4,q5,q6,q7,q8,q9,fk(Random([2..10])),g1,g2,g3,g4,g5,g6,g7,g8>;
	IntMethods := ["DE","GL","CC","Mixed"];
	IntMethods := ["Mixed"];
	AJMethod := ["Direct","Swap"];
	Reductions := ["Real","Complex"];
	for l in [1..10] do
		//f := F[l];
		f := RandomRiemannSurface(Random([2..6]),Random([2..6]):NFDeg:=Random([1..10]));
		P := Random(InfinitePlaces(BaseRing(Parent(f))));
		Chains := MonodromyRepresentation(f,P);
		X := RiemannSurface(f,P:Precision:=Random([30..100]),IntMethod:=Random(IntMethods));
		for k in [1..10] do
			D := RandomDivisor(X,k);
			V := AbelJacobi(D:Reduction:=Random(Reductions));
		end for;
		SE_TestFamilies(Random([2..10]),Random([3..10]):Precision:=Random([30..300]),IntMethod:="Mixed");
		A2 := AJM_Test_2(X);
		if not &and[ Abs(x) lt X`Error : x in Eltseq(A2) ] then
			"A2!",[ Abs(x) lt X`Error : x in Eltseq(A2) ];
			return X;
		end if;
		A3 := AJM_Test_3(X);
		if not &and[ Abs(x) lt X`Error : x in Eltseq(A3) ] then
			"A3:",[ Abs(x) lt X`Error : x in Eltseq(A3) ];
			return X;
		end if;
		FF<v,w> := FunctionField(X);
		A4 := AbelJacobi(Divisor(v),X:Method:=Random(AJMethod));
		if not &and[ Abs(x) lt X`Error : x in Eltseq(A4) ] then
			"A4:",[ Abs(x) : x in Eltseq(A4) ];
			return X;
		end if;
		A5 := AbelJacobi(Divisor(w),X:Method:=Random(AJMethod));
		if not &and[ Abs(x) lt X`Error : x in Eltseq(A4) ] then
			"A5:",[ Abs(x) : x in Eltseq(A5) ];
			return X;
		end if;
	end for;
	return true;
end intrinsic;


intrinsic SE_TestFamilies( m::RngIntElt, n::RngIntElt : Precision := 30, Exact := true, IntMethod := "Mixed" ) -> BoolElt
{ Test superelliptic period matrices for different families of polynomials }
	SetVerbose("RS",2);
	if Exact then
		Kx<x> := PolynomialRing(Rationals());
	else
		C<I> := ComplexField(Precision);
		Kx<x> := PolynomialRing(C);
	end if;		

	// Cyclotomic polynomials
	print "Testing cyclotomic polynomials...";
	C_n := x^n + 1;
	print "C_n:",C_n;
	time S := RiemannSurface(C_n,m:Precision:=Precision,IntMethod:=IntMethod);
	time Tau := SmallPeriodMatrix(S);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	print "A2:",A2;
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	print "Check.";

	// Exponential series
	print "Testing exponential series...";
	E_n := &+[ x^k/Factorial(k) : k in [0..n] ];
	E_n_R := Kx!Reverse(Coefficients(E_n));
	print "E_n:",E_n;
	time S := RiemannSurface(E_n,m:Precision:=Precision,IntMethod:=IntMethod);
	time Tau := SmallPeriodMatrix(S);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	print "A2:",A2;
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	print "E_n_R:",E_n_R;
	time S := RiemannSurface(E_n_R,m:Precision:=Precision,IntMethod:=IntMethod);
	time Tau := SmallPeriodMatrix(S);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	print "A2:",A2;
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	print "Check.";	

	// Bernoulli polynomial
	print "Testing Bernoulli polynomials...";
	B_n := Kx!BernoulliPolynomial(n);
	B_n_R := Kx!Reverse(Coefficients(B_n));
	print "B_n:",B_n;
	time S := RiemannSurface(B_n,m:Precision:=Precision,IntMethod:=IntMethod);
	time Tau := SmallPeriodMatrix(S);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	print "A2:",A2;
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	if Degree(B_n_R) ge 3 then
		print "B_n_R:",B_n_R;
		time S := RiemannSurface(B_n_R,m:Precision:=Precision,IntMethod:=IntMethod);
		time Tau := SmallPeriodMatrix(S);
		/*A := AJM_Test(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
		A2 := AJM_Test_2(S);
		print "A2:",A2;
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
		A3 := AJM_Test_3(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	end if;
	print "Check.";

	//  Legendre polynomials
	print "Testing Legendre polynomials...";
	P_n := (1/2^n) * &+[ Binomial(n,k)^2 * (x-1)^(n-k) * (x+1)^k : k in [0..n] ];
	P_n_R := Kx!Reverse(Coefficients(P_n));
	print "P_n:",P_n;
	time S := RiemannSurface(P_n,m:Precision:=Precision,IntMethod:=IntMethod);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	time Tau := SmallPeriodMatrix(S);
	if Degree(P_n_R) ge 3 then
		print "P_n_R:",P_n_R;
		time S := RiemannSurface(P_n_R,m:Precision:=Precision,IntMethod:=IntMethod);
		time Tau := SmallPeriodMatrix(S);
		/*A := AJM_Test(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
		A2 := AJM_Test_2(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
		A3 := AJM_Test_3(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	end if; 
	print "Check.";
	
	// Laguerre polynomials
	print "Testing Laguerre polynomials...";
	L_n := &+[ Binomial(n,k) * (-1)^k / Factorial(k) * x^k : k in [0..n] ];
	L_n_R := Kx!Reverse(Coefficients(L_n));
	print "L_n:",L_n;
	time S := RiemannSurface(L_n,m:Precision:=Precision,IntMethod:=IntMethod);
	time Tau := SmallPeriodMatrix(S);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	print "L_n_R:",L_n_R;
	time S := RiemannSurface(L_n_R,m:Precision:=Precision,IntMethod:=IntMethod);
	time Tau := SmallPeriodMatrix(S);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	print "Check.";

	// Chebyshev polynomials
	print "Testing Chebyshev polynomials...";
	T_n := &+[ Binomial(n,2*k) * (x^2-1)^k * x^(n-2*k) : k in [0..Floor(n/2)] ];
	T_n_R := Kx!Reverse(Coefficients(T_n));
	print "T_n:",T_n;
	time S := RiemannSurface(T_n,m:Precision:=Precision,IntMethod:=IntMethod);
	time Tau := SmallPeriodMatrix(S);
	/*A := AJM_Test(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
	A2 := AJM_Test_2(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
	A3 := AJM_Test_3(S);
	assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	if Degree(T_n_R) ge 3 then
		print "T_n_R:",T_n_R;
		time S := RiemannSurface(T_n_R,m:Precision:=Precision,IntMethod:=IntMethod);
		time Tau := SmallPeriodMatrix(S);
		/*A := AJM_Test(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A) ];
		A2 := AJM_Test_2(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A2) ];
		A3 := AJM_Test_3(S);
		assert &and[ Abs(x) lt S`Error : x in Eltseq(A3) ];*/
	end if;
	print "Check.";

	return true;
end intrinsic;


/*########################################################################################################
############################    Interesting Test Polynomials    ########################################## 
#########################################################################################################*/

	Z := Integers();
	Q := Rationals();
	Qxy<x,y> := PolynomialRing(Q, 2);

	s := -x^13 - 3*x^12 - 3/2*x^11 + 9/2*x^10 + 13/2*x^9 - 5*x^7 + 6*x^5 + 3*x^4 - 
    7/2*x^3 - 9/2*x^2 - 3/2*x + y^2;

	//f := x^4*y^4 + 2*x^2*y - 2*x*y^2 + 1;
	//fn := x^4*y^4 - x^2*y^4 - x^2*y^2 + y^3 + 1;
	
	// Special curves
	bringscurve := x*(y^5+1) + (x*y)^2 - x^4*y - 2*y^3;

	// Genus 0
	p0 := y^4 - 200*y^2 + 40*y -2 - x;
	p :=  -8094/16177*x^6*y^2 - 1334/4845*x^6*y + 5735/64603*x^5*y 
    - 12570/17063*x^5 - 1111/9960*x^4*y^4 + 4095/8278*x^4 - 41106/40565*x^3*y^5 
    - 8023/26477*x^3*y^4 - 48733/12376*x^2*y^5 - 2075/22463*x^2*y^4 + 
    782/4555*x^2*y + 12133/65500*x^2 + 3291/16613*x*y^5 + 4028/23955*x*y^4 + 
    20971/60040*x*y^3 + 9093/950*x*y^2 + 38487/20558*x*y - 6937/33487*y^2;	

	// Genus 1
	f6 := 2*x*y^2 - x^2 - 1;
	f12 := (x^2 + y^2)^3 + 3*x^2*y - y^3;
	f14 := y^3 -x^2 - 1;
	f17 := (x-1)*y^3 - 2*x^2*y^2 + x*y + 1;
	g13 := -5*x^2*y^2 + 4*x^2*y - x^2 - 5*x*y^2 + 3*x*y + 4*x + 8*y^2 + 9*y + 6;
	g14 := 3*x^2*y^2 - 8*x^2*y - 6*x^2 + 6*x*y^2 - 9*x*y - x - 6*y^2 - 2*y - 6;


	// Genus 2
	f2 := y^3 - x^7 + 2*x^3*y;
	f13 := y^3 + 2*x^7 - x^3*y;
	f23 := -x^2*y^2 - 4*x^2*y + x^2 - 3*x*y^3 + 8*x*y^2 + 2*x*y + 8*x + 2*y^3 - 5*y^2 + 3*y;
	g2 := y^3 + x^4 + x^2;	
	g16 := y^2 - x*(81*x^5 + 396*x^4 + 738*x^3 + 660*x^2 + 269*x + 48);
		

	// Genus 3
	f0 := -5/26*x^4*y + 33/19*x^4 + 13/2*x^3*y^2 + 33/94*x^3 - 24/5*x^2*y^2 - 35/97*x^2*y - 28/81*x^2 - 49/74*x*y + 11/91*x + 11/20*y^2 + 7/20*y - 1/71;
	//f5 := y^3 - (x^2+y)^2 + 1;
	f25 := -9*x^4*y^2 + 7*x^4 - 9*x^3*y^2 + 9*x^3*y - x^2*y^2 - 7*x^2*y - 5*x^2 + 8*x*y^2 - 6*x + 2*y^2 - 2*y - 9;
	f27 := 4*y^4 + 17*x^2*y^2 - (347442520/17751643)*y^2 + (6539/5000)*y^2*x + 4*x^4 + (6539/1250)*x^3 - (457241479/25000000)*x^2 - (6539/1250)*x + (382241479/25000000);
	g1 := y^3 - (x^4 + x^3 - 2*x^2 + 2*x + 4);
	g3 := y^3 - x^4 + 1;
	g6 := y^4 + x^4 - 1;
	g7 := y^7 - x*(1-x)^2;
	g8 := x^2*y^6 + 2*x^3*y^5 - 1;
	g10 := x^3*y^4 + 4*x^2*y^2 + 2*x^3*y - 1;
	g12 := -8*x^4*y^2 - 3*x^4*y + 6*x^4 + 2*x^3*y^2 - 3*x^3*y - 7*x^3 + 2*x^2*y^2 + x^2 - 2*x*y^2 + 2*x*y - 9*x + y^2 - 2*y - 1;
	g15 := x^3*y + y^3 + x;
	f34 := 5*x^3 + 3*x^2 + 10*x*y^2 + x*y + x + y^4 + y^2 + 1;

	// Genus 4
	f1 := y^3 - (x^3+y)^2 + 1;
	f18 := y^3 - x^5 + 2*(10*x-1)^2;

	// Genus 5
	f30 := 2*y^3*x^5 + 5*y^3*x^4 - 3*y^3*x - 9*y^2*x^4 - 4*y^2*x^2 + 3*y*x^3 + 1;
	f35 := -7*x^3*y^4 + 8*x^3*y^2 + 9*x^3*y + 8*x^2*y^3 + 9*x^2*y^2 + 2*x*y^3 + 3;
	
	
	// Genus 6
	f9 := -34*x^2*y^7 + 50*x^2*y^6 - 3*x^2*y^5 - 5*x^2*y^4 + 28*x^2*y^3 - 11*x^2*y^2 + 41*x^2*y - 19*x^2 + 47*x*y^7 - 43*x*y^5 + 14*x*y^4 - 37*x*y^3 + 17*x*y^2 + 27*x*y + x + 6*y^7 + 29*y^6 + 29*y^5 			- 25*y^4 + 14*y^3 - 22*y^2 + 30*y + 43;
	f40 := 17*x^3*y^4 + 10*x^3*y^2 - 7*x^3 + 20*x^2*y^4 + 10*x^2*y^3 - 10*x*y^4 - 7*x*y - 15*x - 7*y^3 + 6*y;

	// Genus 7
	f4 := -11*x^2*y^8 + 38*x^2*y^7 - 2*x^2*y^6 + 2*x^2*y^5 + 23*x^2*y^4 - 42*x^2*y^3 - 18*x^2*y^2 + 15*x^2*y -25*x^2 - 43*x*y^8 - 42*x*y^7 + 20*x*y^6 - 40*x*y^5 - 48*x*y^4 + 40*x*y^3 + 9*x*y^2 - 			10*x*y + 4*x + 29*y^8 - 48*y^7 - 45*y^6 + 31*y^5 + 26*y^4 + 30*y^3 - 6*y^2 + 28*y + 17;
    	f39 := x^6 + x^3*y - x^2*y^3 - 3*x^2*y^2 - 2*x^2*y + 2*x*y^4 + 3*x*y^3 + x*y^2 - y^5 - y^4;

	// Genus 8
	f24 := 7*x^5*y^3 + 4*x^5*y^2 + 2*x^5*y + 9*x^4*y^3 + 4*x^4*y^2 - x^4*y - 9*x^4 - 5*x^3*y^3 + 2*x^3*y^2 - 4*x^3*y + 2*x^2*y^3 + 5*x^2*y^2 - 3*x^2*y + 7*x^2 - 7*x*y^3 + 7*x-4*y^3 + 2*y^2 + 3*y + 4;
	g11 :=  y^8 + x*y^5 + x^4 - x^6;
	g20 := -4*x^3*y^5 - 7*x^3*y^4 + 2*x^3*y^3 + 6*x^3*y^2 - 7*x^3*y - 9*x^3 - 5*x^2*y^5 + 9*x^2*y^4 - 8*x^2*y^3 + 4*x^2*y^2 - 8*x^2*y + 6*x*y^5 + 8*x*y^4 + 6*x*y^3 + 
    		4*x*y^2 + 9*x*y + 2*x + 7*y^5 + 6*y^4 - 6*y^3 + 8*y^2 + 8*y - 2;


	// Genus 9
	f3 := -8*x^4*y^4 + x^4*y^2 - 5*x^4*y - 8*x^4 + x^3*y^3 - 7*x^3*y^2 + 3*x^3*y + 9*x^2*y^4 - 2*x^2*y^3 + 4*x^2*y^2 - 6*x^2 - 5*x*y^4 + 3*y^4 + 3*y^2 - 6;
	f16 := (y^3 - x)*((y-1)^2 -x)*(y-2-x^2) + x^2*y^5;
	g9 := 2*x^7*y + 2*x^7 + y^3 + 3*y^2 + 3*y;

	// Genus 10
	f7 := -2*x^6 + 7*x^5 - 7*x^4 + 5*x^3 + 4*x^2 + 6*x + y^5 - 3;

	// Genus 11
	f10 := -9*x^5*y^4 + 9*x^5*y^3 - 8*x^5*y^2 - 2*x^5*y - 3*x^4*y^4 + 3*x^4*y^2 + 8*x^3*y^2 + 2*x^3 + 8*x^2*y^4 - 5*x^2*y^3 + x^2*y^2 + 2*x*y - 3*y^3;
	f43 := x^6*y^6 + x^3 + y^2 + 1;

	// Genus 12
	g4 := ((y^3 + x^2)^2 + x^3*y^2)^2 + x^2*y^3; // Very hard!
	f20 := 4*x^4*y^4 + 9*x^4*y^2 - 4*x^4*y - 7*x^4 - 3*x^3*y^5 - 3*x^3*y^3 - 2*x^3*y^2 - 8*x^3*y - 2*x^2*y^5 + 9*x^2*y^4 + 
   	       2*x^2*y^3 - 7*x^2*y^2 + 8*x^2 + 3*x*y^5 + 9*x*y^4 - x*y^3 - 3*x*y^2 + 4*x - 8*y^5 - 9*y^4 - y^2 + 2*y + 8; 
	g18 := -3*x^4*y^5 - 3*x^4*y^4 + 7*x^4*y^3 + x^4*y^2 + 9*x^4*y + 4*x^4 - 5*x^3*y^5 + 5*x^3*y^2 + x^3*y - 6*x^3 - 8*x^2*y^5 - 5*x^2*y^4 - 7*x^2*y^3 - x^2*y^2 - 9*x^2*y + 6*x^2 - 8*x*y^5 - 5*x*y^4 			- 8*x*y^3 + 9*x*y^2 + 2*x*y - 7*x + 8*y^5 - 7*y^4 - 8*y^3 - 4*y^2 + 3;

	// Genus 14
	g21 := x^5*y - 100*x^2 + 23*x*y^6 - 10000*x + 1;
	f45 := 15*x^5*y^5 + 44*x^4*y + 24*x^3*y^3 + 15*x*y^4 - 49;

	// Genus 15
	f21 := -30*x^4*y^6 - 2*x^4*y^4 - 38*x^4*y^2 + 25*x^4 + 5*x^3*y^6 - 38*x^3*y^5 + 36*x^3*y + 14*x^3 + 33*x^2*y^6 + 19*x^2*y^5 - 42*x^2*y^4 - 17*x^2*y^2 + 5*x^2*y - 27*x^2 + 9*x*y^6 + 20*x*y^4 + 		21*x*y^3 - 44*x*y^2 + 17*x*y + 35*y^5 + 25*y^4 - 35*y^3 + 33*y^2 + 9;
	f29 := -x^16 - x^15 - 37*x^14 - 145/4*x^13 - 4865/8*x^12 - 9261/16*x^11 - 94253/16*x^10 - 344367/64*x^9 - 9493949/256*x^8 - 4077849/128*x^7 - 20561575/128*x^6 - 4028979/32*x^5 - 25839415/64*x^4 		       - 7905025/32*x^3 - 16556375/32*x^2 - 765625/8*x + y^3 - 3828125/8;

	// Genus 16
	g17 := x^6 + 2*x^4*y^3 + 2*x^2*y^6 + y^9 + y^2;
	g19 := 2*x^5*y^5 - 8*x^5*y^4 - x^5*y^3 + x^5*y^2 - 7*x^5*y + 5*x^5 - 2*x^4*y^5 + 3*x^4*y^4 + 2*x^4*y^3 - 7*x^4*y^2 + x^4*y + 9*x^4 + 6*x^3*y^5 - 5*x^3*y^4 + 7*x^3*y^3 - 7*x^3*y^2 + 2*x^3*y + 			6*x^3 + x^2*y^5 - 5*x^2*y^4 + x^2*y^3 + 7*x^2*y^2 - 8*x^2*y + x^2 - 6*x*y^5 - 5*x*y^4 + 7*x*y^3 - 5*x*y^2 - 3*x*y - 4*x + 2*y^5 - 3*y^4 + y^3 + 7*y^2 + y - 5;

	// Genus 17
	g5 := y^9 + 2*x^2*y^6 + 2*x^4 + x^6 + y^2;
	f5 := x^9 + 2*x^6*y^2 + x^2 + y^6 + 2*y^4;
	
	// Genus 18
	f11 := -17*x^4*y^7 + 13*x^4*y^6 - 19*x^4*y^5 + 4*x^4*y^4 - 6*x^4*y^3 - 5*x^4*y^2 + 15*x^4*y + 15*x^4 + 19*x^3*y^7 - 8*x^3*y^6 + 14*x^3*y^5 + 18*x^3*y^4 - x^3*y^3 + 16*x^3*y^2 + 15*x^3*y - 4*x^3 			+ 10*x^2*y^7 + 7*x^2*y^6 - 12*x^2*y^5 - 10*x^2*y^4 - 7*x^2*y^3 - 15*x^2*y^2 + 5*x^2*y + 13*x^2 + 15*x*y^7 + 9*x*y^6 + 15*x*y^5 + 15*x*y^4 - 16*x*y^3 - 17*x*y^2 - 13*x + 9*y^7 - 12*y^6 - 			2*y^5 - 6*y^4 + 11*y^3 + 2*y^2 - 15*y + 10;

	// Genus 20
	f28 := y^2 - (x^3-1)*(x^7-2^7)*(x^13-3^13)*(x^19-4^19);
	f42 := -17*x^4*y^6 - 28*x^4*y^5 - 11*x^4*y^4 - 27*x^4*y^3 + 8*x^4*y^2 - 14*x^4*y + 12*x^3*y^5 - 25*x^3*y^4 - 13*x^3*y^3 - 18*x^3*y^2 + 14*x^3*y + 18*x^3 - 3*x^2*y^8 + 14*x^2*y^7 + 8*x^2*y^4 + 
    		7*x^2*y^3 + 22*x^2*y - 2*x^2 + 28*x*y^7 + 27*x*y^5 - 20*x*y^4 + 11*x*y^3 + 6*x*y^2 - 10*x*y + 26*x - 11*y^7 - 20*y^6 - 18*y^5 + 17*y^3 + 23*y^2 - y;
	
	// Genus 21
	f32 := 11*x^5*y^3 - 13*x^5*y + 35*x^3*y^7 + 11*x^3*y^5 - 25*x^3*y^3 + 49*x^3*y^2 - 9*x^3 + 11*x^2*y^7 - 40*x^2*y^3 + 29*x*y^7 + 34*x*y^5 - 38*x*y - 20*y^3; 
	f33 := 35*x^7*y^3 + 11*x^7*y^2 + 29*x^7*y + 11*x^5*y^3 + 34*x^5*y + 11*x^3*y^5 - 25*x^3*y^3 - 40*x^3*y^2 - 20*x^3 + 49*x^2*y^3 - 13*x*y^5 - 38*x*y - 9*y^3; // = f32:x<->y
	f26 := -20*x^4*y^8 - 12*x^4*y^7 - 19*x^4*y^6 + 16*x^4*y^5 + 16*x^4*y^3 - 19*x^4*y^2 - 12*x^4*y - 8*x^4 + 3*x^3*y^8 + x^3*y^7 - 8*x^3*y^6 + x^3*y^5 + 11*x^3*y^4 + 
    		19*x^3*y^3 + 12*x^3*y^2 + 16*x^3*y - 6*x^3 + 2*x^2*y^8 - 12*x^2*y^7 - 6*x^2*y^6 - 5*x^2*y^5 - x^2*y^4 - 10*x^2*y^3 + 8*x^2*y^2 + 7*x^2*y + 13*x^2 
    		- 2*x*y^8 + 5*x*y^7 - 2*x*y^6 + 18*x*y^5 + 8*x*y^4 + 13*x*y^3 + 15*x*y^2 - 12*x*y - 17*x - 20*y^8 + 10*y^7 - 10*y^6 + 18*y^5 + 10*y^4 - y^3 + 4*y^2 + 5*y + 14;


	// Genus 22
	f8 := 6*x^12 - 9*x^11 + 8*x^10 - 9*x^9 + 7*x^8 - 7*x^7 + x^6 + 8*x^5 - 2*x^4 + 8*x^3 + 10*x^2 + 9*x + y^5 + 6; 
	f15 := -8*x^12*y^3 - 7*x^12*y^2 + 4*x^12*y + 6*x^12 + 4*x^11*y^3 - 6*x^11*y^2 + x^11*y + 6*x^10*y^3 + x^10*y^2 + 2*x^10*y - 5*x^10 + 6*x^9*y^3 + 7*x^9*y^2 - 7*x^9 + x^8*y^3 - 6*x^8*y^2 + 9*x^8 - 			6*x^7*y^3 + 7*x^7*y^2 + 9*x^7*y + 5*x^7 - 9*x^6*y^3 - 5*x^6*y^2 - x^6*y + 3*x^6 + x^5*y^3 + 4*x^5*y^2 - 2*x^5*y + 5*x^5 + 3*x^4*y^3 - 4*x^4*y^2 + 2*x^4*y - 8*x^4 - 9*x^3*y^3 + 2*x^3*y^2 			+ 7*x^3*y + 3*x^3 - 9*x^2*y^3 - 8*x^2*y^2 + 4*x^2*y + 3*x^2 + 6*x*y^3 - 4*x*y^2 - 2*x*y + 8*x - 2*y^3 + 2*y + 5;	


	// Genus 24
	f36 := -18*x^4*y^9 - 4*x^4*y^8 - 20*x^4*y^7 - 2*x^4*y^6 + 7*x^4*y^5 - 6*x^4*y^4 + 8*x^4*y^2 + 12*x^4*y - 19*x^4 - 17*x^3*y^9 + 8*x^3*y^8 - 20*x^3*y^7 + 13*x^3*y^6 + 13*x^3*y^5 + 6*x^3*y^4 + 			14*x^3*y^3 + 2*x^3*y^2 + 5*x^3*y + 18*x^3 + 9*x^2*y^9 + 18*x^2*y^8 - x^2*y^6 + 6*x^2*y^5 + 8*x^2*y^4 + 6*x^2*y^3 - 2*x^2*y^2 + 5*x^2*y + 10*x^2 + 18*x*y^9 + 3*x*y^8 + 5*x*y^7 - 16*x*y^6 			+ 9*x*y^5 + 7*x*y^4 + 7*x*y^3 + 14*x*y^2 - 14*x*y + 14*x - 19*y^9 - 9*y^8 - 18*y^7 - 12*y^6 + 8*y^5 - 18*y^4 - 15*y^3 + 17*y^2 + 5*y - 2;


	// Genus 28
	f31 := 3*x^5*y^9 + 9*x^5*y^7 - x^4*y^7 + 2*x^4*y^4 + 5*x^3*y^9 + 8*x^2*y^10 - 7*x*y^3 - 6*x - 7*y^7 - 7*y;
	f41 := 4*x^5*y^7 - 20*x^5*y^6 - 9*x^5*y^3 + 14*x^5 - 10*x^4*y^7 + 8*x^4*y^6 + 11*x^4*y^5 + 14*x^4*y^4 - 11*x^4*y^3 + 6*x^4*y - 20*x^4 + 20*x^3*y^7 - 4*x^3*y^5 - 16*x^3*y^4 + 22*x^3*y - 16*x^3 + 			4*x^2*y^8 - 3*x^2*y^7 + 14*x^2*y - 11*x*y^4 + 12*x*y^3 + 14*x*y^2 + 23*x*y - 10*y^7 + 17*y^6 + 14*y^5 + 17*y^4 - 12*y^3 + 13;

	// Genus 30
	f37 := x^6*y^7 - 3*x^6*y^6 + 5*x^6*y^5 + 3*x^6*y^3 + 2*x^6*y - x^6 - 2*x^5*y^7 + 2*x^5*y^4 - 2*x^5*y^3 + 2*x^5*y - x^5 - 4*x^4*y^6 - 5*x^4*y^4 + 4*x^4*y^3 + 5*x^4*y^2 + 4*x^4*y + x^4 - x^3*y^6 - 
    		5*x^3*y^5 - x^3*y^4 - 2*x^3*y^2 - 4*x^3*y - 2*x^2*y^7 - 4*x^2*y^5 - 5*x^2*y^4 - 3*x^2*y^3 + 2*x^2*y^2 - 5*x^2*y - x*y^6 + 5*x*y^5 - 4*x*y^4 + 3*x*y^3 + 4*x*y^2 + 2*x - 5*y^7 - 4*y^6 - 
    		2*y^5 - 3*y^4 - 5*y^2 - y + 1;


	// Genus 36
	f38 := -11*x^5*y^10 + 17*x^5*y^9 - 16*x^5*y^8 + 15*x^5*y^7 + 16*x^5*y^6 + 7*x^5*y^5 + 7*x^5*y^4 + 11*x^5*y^3 + 18*x^5*y^2 - 13*x^5*y + x^5 + 12*x^4*y^10 + 
    		15*x^4*y^9 - 11*x^4*y^8 - x^4*y^7 + 8*x^4*y^6 + 6*x^4*y^5 - 10*x^4*y^4 - 14*x^4*y^3 + 19*x^4*y^2 - 9*x^4*y - 11*x^4 + 15*x^3*y^10 - 12*x^3*y^9 + 
    		7*x^3*y^8 + 9*x^3*y^7 + 4*x^3*y^6 + 20*x^3*y^5 - 12*x^3*y^3 + 20*x^3*y^2 - 9*x^3*y - 6*x^3 - 15*x^2*y^10 - 13*x^2*y^9 - 15*x^2*y^8 + 7*x^2*y^7 - 
    		12*x^2*y^6 - 2*x^2*y^5 + 7*x^2*y^4 + 20*x^2*y^3 - 19*x^2*y^2 + 5*x^2*y + 18*x^2 + 5*x*y^10 - 16*x*y^9 + 4*x*y^8 + 8*x*y^7 - 15*x*y^6 - 12*x*y^5 - 
    		15*x*y^4 - 10*x*y^3 + 15*x*y^2 - 18*x*y - 11*x - y^10 + 19*y^9 + 12*y^8 + 20*y^7 + 19*y^6 + 11*y^5 + 10*y^3 - 16*y^2 - 12*y - 5;

	// Genus 43
	f22 := ((y^4-16)^2-2*x)*y^3 - x^12;
	f44 := y^3*((y^4-16)^2 - 2*x) - x^12;
	
	// Genus 45
	f26 := -1/55572324035428505185378394701824*x^92 + 17615723936275/13893081008857126296344598675456*x^69 - 6625328352560281666119755/55572324035428505185378394701824*x^46 +  			    6624738056749922952079435/6624737266949237011120128*x^23 + y^2 - 1; 
	
	// Genus 54
	f19 := x^9*y^2 + 7*x^9*y + 6*x^8*y^6 - 6*x^8*y^4 - 7*x^7*y - x^6*y^5 - 9*x^6*y^4 - 7*x^6*y^3 - 4*x^6*y^2 + 6*x^5*y^6 + x^5*y^4 + 3*x^5 + 5*x^4*y^8 - 5*x^4*y^6 + x^4*y^5 + 8*x^4*y^4 + 5*x^4*y^3 + 			5*x^4*y^2 - 6*x^3*y^6 + 3*x^3*y^4 - 4*x^3*y^3 + 7*x^3 + x^2*y^9 + 3*x^2*y^6 - 6*x^2*y^4 + 7*x^2*y - 7*x*y^9 - 7*x*y^7 + 8*x*y^2 - 2*x*y + 3*y^5 - 9*y^3; 
		// Very hard.


	// Elliptic curves // g = 1
	e1 := y^2 - (4*x*(x-1)*(x+1));
	e2 := y^2 - (4*(x^3-1));
	e3 := -x^3 + x^2 + 6883*x + y^2 - 222137; 
	e4 := -x^3 - x^2 + 275*x + y^2 - 1667;
	e5 := -x^3 - x^2 + 3*x + y^2 - 9;
	e6 := -x^3 - x^2 + 7*x + y^2 - 8;
	

	// Hyperelliptic curves
	h1 := -x^18 + 3*x^17 - 12*x^16 - 12*x^15 + 9*x^14 + 3*x^13 + 15*x^12 - 7*x^11 + 7*x^10 - 15*x^9 - 8*x^8 + 8*x^7 - 20*x^6 - 4*x^5 + 16*x^4 + 4*x^3 + 5*x^2 + y^2 - 5; // g = 8
	h2 := -x^20 + 9*x^19 + 6*x^18 - 11*x^17 + 6*x^16 - 20*x^15 - 13*x^14 + 11*x^13 + 6*x^12 - 20*x^11 - 8*x^10 - x^9 - 3*x^8 + 11*x^7 - 18*x^6 + 7*x^5 - 4*x^4 - 15*x^3 + 15*x^2 + 8*x + y^2 - 11;
		// g = 9
	h3 := -x^34 - 9*x^33 + 16*x^32 - 6*x^31 - 8*x^30 - 4*x^29 - 10*x^28 + 20*x^27 - 9*x^26 - 12*x^25 + 13*x^24 - 7*x^23 + 19*x^22 - 13*x^21 + x^20 - 15*x^19 - 12*x^18 - 19*x^17 - 14*x^16 + 16*x^15 - 			17*x^14 + 17*x^13 + 19*x^12 - 5*x^11 + 13*x^10 - 16*x^9 - 12*x^8 - x^7 - 20*x^6 - x^5 - 2*x^4 - 6*x^3 - 20*x^2 - 12*x + y^2 - 15; // g = 16
	h4 := -x^35 + 3*x^34 - 20*x^33 + 19*x^32 - 2*x^31 + 12*x^30 - 19*x^29 + 2*x^28 + 4*x^27 + 7*x^26 + 7*x^25 + 12*x^24 - 5*x^23 - 5*x^22 + 16*x^21 + 7*x^20 - 13*x^19 + 2*x^18 - 10*x^17 - 11*x^16 - 			5*x^15 + 10*x^14 - 16*x^13 - 18*x^12 + 6*x^11 - x^10 + 2*x^9 - 10*x^8 - 16*x^7 - 13*x^6 + 6*x^5 + 4*x^4 + 12*x^3 + 15*x^2 - 6*x + y^2 + 7; // g = 17
	h5 := -x^48 + 17*x^46 + 9*x^45 - 10*x^44 + 9*x^43 - 9*x^42 - 17*x^41 + 16*x^40 + 2*x^39 + 9*x^38 - 7*x^37 - 13*x^36 - 18*x^35 + 16*x^34 + 18*x^33 + 5*x^32 - 3*x^31 + 3*x^30 - 
    		5*x^29 - 8*x^28 + 15*x^27 + x^26 + 10*x^25 - 8*x^24 + 16*x^22 + 14*x^21 - 3*x^20 - 10*x^19 + 19*x^18 + 7*x^17 - 19*x^16 - 5*x^15 + 12*x^14 + 13*x^13 - x^12 + 16*x^11 - x^10 + 6*x^9 + 			20*x^8 - 20*x^7 + 8*x^6 - 13*x^5 - 4*x^4 - 17*x^3 + 19*x^2 + 13*x + y^2 + 12; // g = 23
	h6 := -x^50 - 9*x^49 - 20*x^48 + 20*x^47 - 12*x^46 + 18*x^45 - 7*x^44 - 3*x^43 - 7*x^42 - 16*x^41 + 13*x^40 - 7*x^39 + 3*x^38 + 17*x^37 + 7*x^36 + 11*x^35 - 19*x^34 + 15*x^33 - 7*x^32 + 11*x^31 			- 14*x^30 - 8*x^29 - 9*x^28 - 11*x^27 + 16*x^26 + 2*x^25 - 8*x^24 + 16*x^23 + 9*x^22 + 10*x^21 + 10*x^20 + 10*x^19 - 14*x^18 + 15*x^17 + 18*x^16 - 11*x^15 + 9*x^14 - 11*x^13 - 13*x^12 - 			3*x^11 + 16*x^10 - 17*x^9 + 10*x^8 + x^7 - 3*x^6 - 10*x^5 + 7*x^4 + 4*x^3 + 12*x^2 - 8*x + y^2 + 8; // g = 24
	h7 := -x^68 - 16*x^67 - 3*x^66 - 12*x^65 + 14*x^64 + 15*x^63 + 14*x^62 + 17*x^61 + 17*x^60 - 14*x^59 - 5*x^58 + 6*x^57 - 8*x^56 - 3*x^54 + 20*x^53 - 7*x^52 + 12*x^51 + x^50 + 6*x^49 + 20*x^48 - 
    		15*x^47 + 9*x^46 - 18*x^45 - 11*x^44 + 3*x^43 - 10*x^42 - 13*x^41 - 18*x^40 + 19*x^39 - 10*x^38 + 14*x^37 - 3*x^36 - 9*x^35 + 5*x^34 + 14*x^33 + 19*x^32 + 5*x^31 + 9*x^30 - 9*x^29 - 			3*x^28 + 19*x^27 + 18*x^25 - 4*x^24 + 17*x^23 - 3*x^22 - 19*x^21 - 17*x^20 + 16*x^19 + 7*x^18 - 16*x^17 - 9*x^16 + 12*x^15 - 13*x^14 - 19*x^13 + 10*x^12 + 7*x^11 - 19*x^10 + 14*x^9 - 			7*x^8 + 6*x^7 - 18*x^6 - 9*x^5 + 7*x^4 + 15*x^3 + 10*x^2 + 19*x + y^2 - 8; // g = 33;
	h8 := -x^70 + 8*x^69 - x^68 - x^67 + 11*x^66 - x^65 + 4*x^64 + 16*x^63 - 16*x^62 + 7*x^61 - 9*x^60 + 17*x^59 - 19*x^58 - 7*x^57 - 2*x^56 + 7*x^55 - 2*x^53 + 17*x^52 + 5*x^51 + 7*x^50 - 10*x^49 + 			18*x^48 + 19*x^47 + 6*x^46 + x^45 - 5*x^44 + 14*x^43 + 2*x^42 - 20*x^41 + 4*x^40 - 4*x^39 + 15*x^38 - 10*x^37 - 2*x^36 - 18*x^35 - 8*x^34 + 17*x^33 - 18*x^32 - 18*x^31 - 12*x^30 + 			12*x^29 + 19*x^28 - 11*x^27 - 5*x^26 - 13*x^25 - 15*x^24 - 14*x^23 - x^22 + 8*x^21 - 2*x^20 + 16*x^19 - 3*x^18 + 4*x^17 - 11*x^16 - 5*x^15 + 4*x^14 - 11*x^13 - 16*x^12 + 12*x^11 + 			14*x^10 - 2*x^9 - 10*x^8 + 15*x^7 - 10*x^6 + 10*x^5 + 14*x^4 + 18*x^3 - 14*x^2 + 8*x + y^2 - 9; // g = 34;
	h9 := -x^100 + 22*x^99 - 16*x^98 + 19*x^97 + 17*x^96 + 34*x^95 + 36*x^94 - 40*x^93 - 17*x^92 + 9*x^91 + 13*x^90 - 17*x^89 + 39*x^88 + 6*x^87 - 16*x^86 + 40*x^85
    		+ 34*x^84 - 21*x^83 - 21*x^82 + 7*x^81 - 5*x^80 + 45*x^79 - 42*x^78 - 47*x^77 + 9*x^76 - 48*x^75 - 23*x^74 + 7*x^73 + 15*x^72 - 40*x^71 - 41*x^70 + 
  		  40*x^69 - 39*x^68 - 39*x^67 - 45*x^66 + 26*x^65 - 50*x^64 - 35*x^63 - 30*x^62 + 43*x^61 - 22*x^60 - 20*x^59 - 6*x^58 + 15*x^57 - 44*x^56 + 6*x^55 - 
		    37*x^54 - 28*x^53 + 50*x^52 - 19*x^51 - 44*x^50 - 35*x^49 - 37*x^48 + 14*x^47 - 39*x^46 - 49*x^45 + 29*x^44 - 14*x^43 - 31*x^42 + 33*x^41 - 27*x^40 + 
		    8*x^39 - 48*x^38 + 8*x^37 + 27*x^36 - 14*x^35 + 8*x^34 - 42*x^33 + 20*x^32 - 3*x^31 - 15*x^30 - 47*x^29 + 36*x^28 + 2*x^27 - 14*x^26 + 8*x^25 + 
		    23*x^24 + 40*x^23 + 39*x^22 - 18*x^21 - 42*x^20 + 16*x^19 + 3*x^18 - 29*x^17 - 9*x^16 - 42*x^15 - 6*x^14 - 13*x^13 - 27*x^12 + 18*x^11 + 16*x^10 - 
		    10*x^9 - 8*x^8 - 4*x^7 + 29*x^6 + 17*x^5 + 50*x^4 + 30*x^3 + 39*x^2 + 40*x + y^2 + 37; // g = 49

	// Superelliptic curves
	s1 := -x^5 + 7*x^4 + 3*x^3 - 3*x^2 - 13*x + y^6 - 20; // g = 10
	s2 := -x^10 - x^9 - 6*x^8 + 8*x^7 - 14*x^6 + 14*x^5 - 13*x^4 + 10*x^3 + 15*x^2 + 8*x + y^5 - 11; // g = 16
	s3 := -x^12 + 20*x^11 + 15*x^10 - 3*x^9 - 15*x^8 - 6*x^7 - 7*x^6 + 3*x^5 - 16*x^4 - 6*x^3 - 6*x^2 + 20*x + y^6 + 15; // g = 25
	s4 := -x^15 - 9*x^14 - 8*x^13 + 4*x^12 + 2*x^11 + 17*x^10 - 9*x^9 - 20*x^8 + 14*x^7 + 16*x^6 - 3*x^5 + 13*x^4 - 14*x^3 + 6*x^2 - 8*x + y^10 + 9; // g = 61
	s5 := -x^20 - 14*x^19 + 17*x^18 - x^17 - 16*x^16 + 6*x^15 + 15*x^14 + 18*x^13 + 3*x^12 - 9*x^11 + 4*x^10 + 10*x^9 + 19*x^8 + 5*x^7 - 20*x^6 - x^5 + 19*x^4 + 9*x^3 - 16*x^2 + 6*x + y^10 + 18; 
		// g = 81
	s6 := -x^30 + 16*x^29 + 9*x^28 - 13*x^27 + 5*x^26 - 17*x^25 + 7*x^24 + 20*x^23 - 10*x^22 - 10*x^21 + 6*x^20 - 20*x^19 + x^18 - 3*x^17 + 6*x^16 + 6*x^15 + 2*x^14 - 16*x^13 - x^12 + 6*x^11 + 			12*x^10 + 8*x^9 - 15*x^8 + 17*x^7 + 19*x^6 - 3*x^5 - 18*x^4 - 4*x^3 - 11*x^2 + 10*x + y^10 + 7; // g = 126
	s7 := -x^30 - 12*x^29 - 20*x^28 + x^27 + 13*x^26 + x^25 + 12*x^24 + 15*x^23 - 3*x^22 - 17*x^21 - x^20 + 5*x^19 - 7*x^18 + 18*x^17 + 
    		7*x^16 - 7*x^15 - 11*x^14 + 13*x^13 - 2*x^12 + 7*x^11 + 10*x^10 - 7*x^9 + 20*x^8 + 12*x^7 - 16*x^6 - 6*x^5 + 14*x^4 + 20*x^3 - 7*x^2 + x + y^15 + 6; // g = 196
	s8 := -x^30 - 7*x^29 - 15*x^28 - 9*x^27 - 16*x^26 + 9*x^25 + x^24 - 6*x^23 + 4*x^22 - 8*x^21 - 15*x^20 - 19*x^19 - 18*x^18 + 12*x^17 - 8*x^16 + x^15 - 3*x^14 - 
    		15*x^13 + 20*x^12 - 15*x^11 - 11*x^10 + 2*x^9 - 9*x^8 + 11*x^7 + 13*x^6 + 11*x^5 + 13*x^4 + 4*x^3 + 16*x + y^20 - 11; // g = 271
	s9 := -x^35 - 39*x^34 - 48*x^33 + 12*x^32 - 6*x^31 + 30*x^30 - 12*x^29 - 28*x^28 + 33*x^27 - 48*x^26 - 2*x^25 - 7*x^24 - 27*x^23 + 27*x^22 - 7*x^21 - 12*x^20 -
    		14*x^19 + 44*x^18 - 42*x^17 + 14*x^16 + 42*x^15 - 30*x^14 - 33*x^13 + 48*x^12 - 8*x^10 - 34*x^9 + 8*x^8 + 16*x^7 - 17*x^6 - 26*x^5 + 38*x^4 + 13*x^3 - 22*x^2 + 32*x + y^21 - 2; // g = 337
	s10 := -x^40 - 40*x^39 + 39*x^38 - 48*x^37 + 4*x^36 + 31*x^35 + 22*x^34 + 17*x^33 - 24*x^32 - 4*x^31 - 13*x^30 - 19*x^29 + 50*x^28 + 39*x^27 + 21*x^26 - 21*x^25
    	- 25*x^24 + 14*x^23 + 22*x^22 + 10*x^21 + 40*x^20 - 31*x^19 + 34*x^18 - 4*x^17 + 39*x^16 - 42*x^15 + 47*x^14 - 28*x^13 + 35*x^12 + 5*x^11 - 40*x^10 
    	- 9*x^9 - 28*x^8 - 9*x^7 + 14*x^6 + 34*x^5 + 7*x^4 + 8*x^3 - 28*x^2 + 43*x + y^23 + 11; // g = 429
	s11 := -x^28 + 2*x^27 - x^26 + x^25 + 2*x^23 - 2*x^22 + x^21 - x^20 - x^19 + 2*x^17 - 2*x^15 - 2*x^13 - x^12 + x^11 - 2*x^10 - x^9 - 2*x^8 + x^7 + 2*x^5 - 2*x^4 -
    		x^3 + x^2 - x + y^3;

	// Quartics // g = 3
	q1 := -4*x^4 - 5*x^3*y + x^3 + 2*x^2*y^2 - 5*x^2*y + 3*x^2 + 3*x*y^3 + x*y - 5*x - 8*y^3 - 3;
	q2 := -x^4 + 8*x^3*y - 6*x^3 - 3*x^2*y^2 - 9*x^2 + 8*x*y^3 - 3*x*y^2 + 2*x*y + 4*y^3 + 2*y^2 + 4;
	q3 := 6*x^3*y + 6*x^3 - x^2*y^2 - x^2*y - 6*x^2 - 4*x*y^3 + 2*x*y^2 + 2*x - 7*y^3 - 5*y^2 + 3;
	q4 := -5*x^4 - 3*x^3*y + 9*x^2*y^2 - 4*x^2*y + 9*x*y^3 + 4*x*y^2 - 4*x*y + x - 9*y^3 + 7*y^2 + 9*y + 5;
	q5 := 7*x^3*y - x^3 - 8*x^2*y^2 - 3*x*y + 2*x + 9*y^4 - 6*y^2 + 2*y;
	q6 := 5*x^3*y - 6*x^3 + 7*x^2*y^2 + 7*x^2 - x*y^3 - 8*x*y^2 - x*y - 5*x + 5*y^4 + 9*y^3 + 9*y^2 - 2*y + 7;

	// Examples for integration
	i1 := 11*x^3 - 12*x^2*y^2 + 33*x^2 - 28*x - 39*y^2 - 14*y + 22;

	// CM curves
	// Hyperelliptic, g = 2
	cm1 := y^2 - (x^5 - 1);
	cm2 := y^2 - (-x^5 + 3*x^4 + 2*x^3 - 6*x^2 - 3*x + 1);
	cm3 := y^2 - (-11*x^6 - 2*x^5 - x^4 + 4*x^3 + 7*x^2 - 6*x + 1);
	cm4 := y^2 - (-8*x^6 + 52*x^5 - 250*x^3 + 321*x + 131);
	cm5 := y^2 - (-8*x^6 - 64*x^5 + 1120*x^4 + 4760*x^3 - 48400*x^2 + 22627*x - 91839);
	cm6 := y^2 - (79888*x^6 + 293172*x^5 - 348400*x^3 - 29744*x + 103259);
	cm7 := y^2 - (289*x^6 + 242*x^5 - 225*x^4 - 92*x^3 + 87*x^2 - 42*x - 43);
	cm8 := y^2 - (-444408*x^6 + 6986711*x^5 + 44310170*x^4 - 582800*x^3 + 2656360*x^2 - 8866880*x + 2160600);

	// Quartics, g = 3
	cmx1 := -4169*x^4 - 956*x^3*y + 7440*x^3 + 55770*x^2*y^2 + 43486*x^2*y + 42796*x^2 - 38748*x*y^3 - 30668*x*y^2 + 79352*x*y - 162240*x + 6095*y^4 + 19886*y^3 - 89869*y^2 -
		1079572*y - 6084;
	cmx2 := 19*x^4 + 80*x^3*y - 54*x^3 - 24*x^2*y^2 - 34*x^2*y + 77*x^2 - 88*x*y^3 - 28*x*y^2 + 38*x*y + 516*x + 30*y^4 - 36*y^3 - 135*y^2 + 452*y + 4;
	cmx3 := -1210961*x^4 + 5202144*x^3*y + 408700*x^3 - 2479108*x^2*y^2 + 1908050*x^2*y + 8367272*x^2 - 4393072*x*y^3 - 6944000*x*y^2 + 6772756*x*y + 10594064*x + 4978166*y^4
		- 8342100*y^3 + 4611839*y^2 + 14080572*y - 1387684;
	cmx4 := 115*x^4 - 766*x^3*y - 1336*x^3 + 1205*x^2*y^2 + 5187*x^2*y + 4040*x^2 + 8216*x*y^3 + 1322*x*y^2 - 9484*x*y + 1144*x - 8094*y^4 + 9032*y^3 + 9669*y^2 - 6292*y - 4706;
	cmx19 := -7*x^4 - 2*x^3*y + 16*x^3 + 7*x^2*y^2 - 6*x^2*y - 8*x^2 + 10*x*y^3 + 14*x*y^2 + 2*x*y - 15*x + y^4 + 10*y^3 + 13*y^2 + 17*y + 14;

	// Not in list: f19, g21
	List := [ f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39,
	f40, f41, f42, f43, f44, f45, g1, g2, g3, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, q1, q2, q3, q4, q5, q6, h1, h2, h3, h4, h5, h6, h7, h8, h9, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, i1 ];

	// Fail!
	sf1 := 10*x^2*y^2 + 17*x^2 - 7*x*y^2 - 12*x + 26*y^2 + 10;
	sf2 := x^4 + x^3*y + 2*x^3 - 6*x^2*y^2 + 3*x^2*y - 6*x*y^3 + 3*x*y
- 2*x + 4*y^4 + 5*y^3 - 3*y^2 - 3*y + 1;

	vh1 := 17/26*x^5*y^2 - 3*x^5 + 10/13*x^4*y^2 + 41/17*x^4 + 
    36/55*x^3*y^2 + 1/5*x^3*y + 23/2*x^3 + 14/41*x^2*y - 9/23*x*y + 17/22*y^2 - 
    1/5*y + 47/4;

/*#########################################################################################################
Parametrized D5-Family, Status: Check
#########################################################################################################*/

function f_ab( alpha, beta )
	a := 5 * alpha^4 / 4 * (beta^2+1)^2 * (beta^2+beta-1) * (beta^2 - beta - 1);
	b := alpha^5 / 2 * (beta^2+1)^3 * (beta^2 + beta - 1) * (2*beta - 1) * (beta + 2);
	f := y^5 + a*y + b;
	return f;
end function;


function f_fam(n)
	d := n-1;
	f := (x + y)^d + x^2*y^n + x*y  + 1;
	print "Genus:",Genus(FunctionField(f));
	return f;
end function;

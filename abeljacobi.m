/*******************************************************************************

	Abel-Jacobi map for Riemann surfaces
 
	Christian Neurohr, June 2019

*******************************************************************************/

import "integration.m": GL_Integration, CC_Integration, GLCC_Params_Path, DE_Integration, DE_Params_Path, HeuristicBound, SE_Integrals_Edge_AJM, SE_DE_Integration, SE_GJ_Integration;
import "infinitepoints.m": SpecialPointsByMoving, AJM_DE_InfinitePoints, SE_AJM_InftyPoints;
import "fundamentalgroup.m": SE_Edge, EdgeData, Mixed_Params_AJM;
import "analyticcontinuation.m": AC_mthRoot;
import "paths.m": CLineSegment, CArc, CFullCircle, ReversePath, PermuteMatrix, IntersectionPoints;
import "miscellaneous.m": CompareByFirstEntry, IsWeaklyIn, MakeCCVector, SE_DKPEB, EmbedPolynomial, ModifiedFiber;
import "periodmatrix.m": ReductionMatrix;
import "riesrfclass.m": SwappedSurface;

function PeriodLatticeReductionReal(V,X)
/* Reduce V \in \C^g modulo period matrix (A,B) to an element of R^(2g)/Z^(2g) */
	g := X`Genus; 
	m := NumberOfColumns(V);
	R := BaseRing(Parent(X`ReductionMatrixReal));
	W := Matrix(R,2*g,m,[]);
	for k in [1..m] do
		for l in [1..g] do
			W[l][k] := Re(V[l][k]);
			W[l+g][k] := Im(V[l][k]);
		end for;
	end for;
	/* Assume now V in \R^(m x 2g) */
	W := X`ReductionMatrixReal * W;
	return Matrix(R,2*g,m,[w - Round(w) : w in Eltseq(W)]);
end function;
function PeriodLatticeReductionComplex(V,X)
/* Reduce V \in \C^g modulo period matrix (A,B) to an element of C^g/<1,Tau> */
	g := X`Genus;
	m := NumberOfColumns(V);
	C<I> := BaseRing(Parent(V));
	Tau := ChangeRing(X`SmallPeriodMatrix,C);
	V := X`ReductionMatricesComplex[1] * V;
	W := X`ReductionMatricesComplex[2] * Matrix(g,m,[Im(v) : v in Eltseq(V)]);
	V1 := Matrix(C,g,m,[Round(w) : w in Eltseq(W)]);
	V -:= Tau * V1;
	return V - Matrix(C,g,m,[Round(Re(v)) : v in Eltseq(V)]);
end function;


/* Abel-Jacobi map for superelliptic Riemann surfaces */

procedure SE_TreeMatrix(X)
/* Computes a 'tree-matrix' which contains paths in the spanning tree connecting P_0 -> P_i for all ramification points P_i */
	if not assigned X`TreeMatrix then
	n := X`Degree[2];
	TM := ZeroMatrix(Integers(),n,n-1);
	Taken := [ 0 : j in [1..n] ];
	Tree := X`SpanningTree`Edges;
	P_0 := Tree[1]`EP[1];
	Taken[P_0] := 1;
	for j in [1..n-1] do
		if Taken[Tree[j]`EP[1]] eq 1 then
			PStart := Tree[j]`EP[1];
			PEnd := Tree[j]`EP[2];
			Taken[Tree[j]`EP[2]] := 1;
		else
			PStart := Tree[j]`EP[2];
			PEnd := Tree[j]`EP[1];
			Taken[Tree[j]`EP[1]] := 1;
		end if;
		TM[PEnd] := TM[PStart];
      		TM[PEnd,j] := 1;
	end for;
	/* Shift by basepoint for Abel-Jacobi map */
	P_0P_0 := TM[1];
	for j in [1..n] do
		TM[j] -:= P_0P_0;
	end for;
	X`TreeMatrix := TM;
	end if;
end procedure;
		
procedure SE_RamificationPoints_AJM(X)
/* Computes the Abel-Jacobi map of the divisors D_i = [ P_i - P_0 ] for i = 1,...,n and of D = [ \sum_{j = 0}^{delta} P_{\infty}^j - \delta P_0 ] */
	g := X`Genus;
	m := X`Degree[1]; 
	n := X`Degree[2];
	if not assigned X`AJM_RamificationPoints then
		AJMRamPoints := [];
		for j in [1..n] do
			V := Matrix(X`ComplexFields[2],g,1,[]);
			TreePath := X`TreeMatrix[j];
			for k in [1..n-1] do
				V +:= ChangeRing(X`ElementaryIntegrals[k] * TreePath[k],X`ComplexFields[2]);
			end for;
			Append(~AJMRamPoints,V);
			
		end for;
		X`AJM_RamificationPoints := AJMRamPoints;
	end if;
	if not assigned X`AJM_SumOfInftyPoints then
		delta,a,b := Xgcd(m,n);
		X`AJM_SumOfInftyPoints := b * &+[ V : V in X`AJM_RamificationPoints ];
	end if;
end procedure; 


/* Abel-Jacobi map for Riemann surfaces over number fields */
function AbsSquared(w)
	return Re(w)^2+Im(w)^2;
end function;
function DistSquared(Z)
	DistsSquared := []; m := #Z;
	for k in [1..m] do
		for kk in [k+1..m] do
			Append(~DistsSquared,AbsSquared(Z[k]-Z[kk]));
		end for;
	end for;
	return Min(DistsSquared);
end function;
function AJM_DKPEB( f,Z,Digits : Infty:=true )
/* A posteriori erround bound method for Abel-Jacobi map */
	m := Degree(f);
	RMV := [ Remove([1..m],j) : j in [1..m] ];
	/* Start root approximation */
	W := [ Evaluate(f,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
	Err2 := Real(((1/2) * 10^-(Digits+1))^2); // Error^2
	w0 := Max( [ AbsSquared(W[j]) : j in [1..m] ]); // w0^2
	NextError := w0;
	LastError := Infinity();
	if Infty or 16*w0 le DistSquared(Z) then
		while NextError gt Err2 and NextError lt LastError do
			Z := [ Z[j] - W[j] : j in [1..m] ];
			W := [ Evaluate(f,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
			LastError := NextError;
			NextError := Max( [ AbsSquared(W[j]) : j in [1..m] ]);
		end while;
		return Z;
	else
		return [];
	end if;
end function;
function AJM_Recursion(f,x1,x2,Fiber_x1:Digits:=Precision(x1),Infty:=true)
/* Analytically continue the fiber above Gamma(t1) to the fiber above Gamma(t2) */
	f_x2 := Evaluate(f,[x2,PolynomialRing(Parent(x2)).1]);
	f_x2 *:= 1/LeadingCoefficient(f_x2);
	Fiber_x2 := AJM_DKPEB(f_x2,Fiber_x1,Digits:Infty:=Infty);
	if #Fiber_x2 gt 0 then
		return Fiber_x2;
	else
		Fiber_x1_1 := AJM_Recursion(f,x1,(x1+x2)/2,Fiber_x1:Digits:=Digits,Infty:=Infty);
		Fiber_x2 := AJM_Recursion(f,(x1+x2)/2,x2,Fiber_x1_1:Digits:=Digits,Infty:=Infty);
		return Fiber_x2;
	end if;
end function;

procedure AJM_DE_DiscriminantPoint(Gamma,k,X,TestChain)
/* Compute the Abel-Jacobi map from the basepoint to the endpoint of Gamma on all sheets using double-exponential integration */
	vprint RS,1 :  "Integrating to center of chain",X`ClosedChains[k];
	NewPrec := true;
	go_on := true;
	CL := ComplexField(5);
	Err := 10^-(Precision(X`ComplexFields[2])+1);
	c := Max([ #cd : cd in  CycleDecomposition(X`ClosedChains[k]`Permutation) ])+1;
	assert c gt 1;
	m := X`Degree[1];
	RMV := [ Remove([1..m],j) : j in [1..m] ];
	Digits := Precision(X`ComplexFields[2]);
	Err2 :=  Err^2/4; // Error^2
	g := X`Genus;
	h := 16/125;
	OldError := Infinity();
	Gammas := [];
	while go_on do
		go_on := false;
		if NewPrec then
			CC<I> := ComplexField(c*Precision(X`ComplexFields[3]));
			RR := RealField(CC);
			Cz<z> := PolynomialRing(CC);
			Cxy<x,y> := PolynomialRing(CC,2);
			fC := EmbedPolynomial(X`DefiningPolynomial,X`Embedding,Cxy);
			/* Differentials */
			if X`Baker then
				DFF_Factors := [ Derivative(fC,2) ];
			else
				DFF_Factors := [ EmbedPolynomial(Fac,X`Embedding,Cxy) : Fac in X`HolomorphicDifferentials[1] ];
			end if;
		end if;
		NGamma := CLineSegment(CC!Gamma`StartPt,CC!Gamma`EndPt);

		/* Compute double-exponential integration */
		N := Round(7.2/h);
		N2P1 := 2*N+1;
		Abscissas, Weights := TanhSinhIntegrationPoints( N, RR!h );
		Append(~Abscissas,1);
		
		/* Integrate path to infinity */
		PathDiffMatrix := Matrix(CC,m,g,[]);
		xj, dxj := NGamma`Evaluate(Abscissas[1]);
		yj := ModifiedFiber(fC,NGamma`StartPt);
		pxj := Evaluate(fC,[xj,z]);
		pxj *:= 1/LeadingCoefficient(pxj);
		W := [ Evaluate(pxj,yj[i])/ &*[ (yj[i] - yj[k]) : k in RMV[i] ] : i in [1..m] ];
		w0 := Max( [  Re(W[i])^2 + Im(W[i])^2 : i in [1..m] ]);
		NextError := w0;
		LastError := Infinity();
		while NextError gt Err2 and NextError lt LastError do
			yj := [ yj[i] - W[i] : i in [1..m] ];
			W := [ Evaluate(pxj,yj[i])/ &*[ (yj[i] - yj[k]) : k in RMV[i] ] : i in [1..m] ];
			LastError := NextError;
			NextError := Max( [ Re(W[i])^2 + Im(W[i])^2 : i in [1..m] ]);
		end while;
		for j in [1..N2P1] do
			OneMat := X`DFFEvaluate(DFF_Factors,xj,yj,m);
			OneMat *:= (Weights[j] * dxj);
			MAXABS := Max([Abs(c):c in Eltseq(ChangeRing(OneMat,CL))]);
			if (MAXABS lt Err and j gt N) or Abscissas[j+1] eq 1 then
				break j;
			end if;
			PathDiffMatrix +:= OneMat;
			xj, dxj := NGamma`Evaluate(Abscissas[j+1]);
			pxj := Evaluate(fC,[xj,z]);
			pxj *:= 1/LeadingCoefficient(pxj);
			W := [ Evaluate(pxj,yj[i])/ &*[ (yj[i] - yj[k]) : k in RMV[i] ] : i in [1..m] ];
			w0 := Max( [  Re(W[i])^2 + Im(W[i])^2 : i in [1..m] ]);
			NextError := w0;
			LastError := Infinity();
			while NextError gt Err2 and NextError lt LastError do
				yj := [ yj[i] - W[i] : i in [1..m] ];
				W := [ Evaluate(pxj,yj[i])/ &*[ (yj[i] - yj[k]) : k in RMV[i] ] : i in [1..m] ];
				LastError := NextError;
				NextError := Max( [ Re(W[i])^2 + Im(W[i])^2 : i in [1..m] ]);
			end while;
			if NextError gt X`Error and NextError ge LastError then
				go_on := true; c +:= 1; NewPrec := true; h := h/2; break j;
			end if;
		end for;
		NGamma`Integrals := ChangeRing(PathDiffMatrix,X`ComplexFields[3]);
		Append(~Gammas,NGamma);	

		/* How many correct digits? */
		if go_on eq false then
			vprint RS,2 :  "Testing accuracy...";
			if TestChain`Permutation ne Id(Sym(m)) then
				V := NGamma`Integrals - PermuteMatrix(NGamma`Integrals,TestChain`Permutation,m,g) -  TestChain`Integrals;
				vprint RS,3 : "V:",V;
				NGamma`Error := Max([ Abs(c) : c in Eltseq(V) ]);
				MABS := Floor(-Log(10,NGamma`Error));
				vprint RS,2 : "Significant digits in AJM_DE_DiscriminantPoint:",MABS;
				if NGamma`Error gt X`Error then
					if NGamma`Error/OldError gt 1/10 and #Gammas gt 2 then
						print "Warning! Significant digits for integral to discriminant point:",MABS;
						go_on := false;
						break;
					else
						h := h/2;
						go_on := true;
						OldError := NGamma`Error;
						NewPrec := false;
					end if;
				end if;
			else
				s := #Gammas;
				if s eq 1 then
					go_on := true; h := h/2; NewPrec := false;
				else
					NGamma`Error := Max([ Abs(c) : c in Eltseq(Gammas[s]`Integrals-Gammas[s-1]`Integrals) ]);
					MABS := Floor(-Log(10,NGamma`Error));
					vprint RS,2 : "Significant digits in AJM_DiscriminantPoints:",MABS;
					if NGamma`Error gt X`Error then
						go_on := true; h := h/2; NewPrec := false;
					else
						go_on := false;
					end if;
				end if;
			end if;
		end if;
		for k in [1..X`Genus] do
			Val := Abs(&+[ z : z in Eltseq(ColumnSubmatrix(PathDiffMatrix,k,1))]);
			if Val gt X`Error then
				go_on := true;
			end if;
		end for;
	end while;
	
	/* Error, permutation & sheets */
	Gamma`Error := NGamma`Error;
	Ok, Sigma := Sort(yj,X`Ordering);
	Gamma`Permutation := Inverse(Sigma);
	Gamma`Sheets := yj;

	/* Save integrals at reasonable precision */
	Gamma`Integrals := ChangeRing(PathDiffMatrix,X`ComplexFields[3]);
end procedure;


procedure AJM_DiscriminantPoints(X,k)
/* Compute Abel-Jacobi map to discriminant point by brute force double-exponential integration */
	Ch := X`ClosedChains[k];
	l := 1;
	while not assigned Ch`Paths[l]`Center or Ch`Paths[l]`Center ne Ch`Center do
		l +:= 1;
	end while;
	TestChainPaths := [];
	while assigned Ch`Paths[l]`Center do
		Append(~TestChainPaths,Ch`Paths[l]);
		l +:= 1;
	end while;
	TestChain := Chain(TestChainPaths);
	PathToCenter := Append(Ch`Paths[1..l-1],CLineSegment(Ch`Paths[l-1]`EndPt,Ch`Center));

	/* Actual integration */
	AJM_DE_DiscriminantPoint(PathToCenter[l],k,X,TestChain);
	ChainToCenter := Chain(PathToCenter);
	Perm := &*[ PathToCenter[k]`Permutation : k in [1..l-1] ];
	ChainToCenter`Sheets := [ PathToCenter[l]`Sheets[k^Perm] : k in [1..X`Degree[1]] ];

	/* Save chain to discriminant point */
	X`AJM_DiscriminantPoints[k] := ChainToCenter;

	/* How many correct digits? */
	vprint RS,2 :  "Testing accuracy...";
	Value := ChainToCenter`Integrals - PermuteMatrix(ChainToCenter`Integrals,Ch`Permutation,X`Degree[1],X`Genus);
	Value -:= Ch`Integrals;
	vprint RS,3 : "Value:",Value;
	MABS := Min( [ Floor(-Log(10,Abs(c))) : c in Eltseq(Value) | c ne 0 ]);
	vprint RS,2 : "Significant digits in AJM_DiscriminantPoints:",MABS;
end procedure;


function FindPathOnSheet(Gamma,X);
/* Replace Gamma by NewPath (a path avoiding discriminant points) */
	assert Gamma`Type eq "LineSegment";
	IntPoints := []; DP := X`DiscriminantPoints;
	for j in [1..#DP] do
		DPt := DP[j];
		FC := CFullCircle(DPt-X`SafeRadii[j],DPt);
		Intersect, IntPts := IntersectionPoints(Gamma,FC);
		if Intersect then
			Append(~IntPoints,<j,IntPts[1],IntPts[2]>);
		end if;
	end for;
	Sort(~IntPoints,CompareByFirstEntry);
	NewPath := [Gamma];
	BPx := X`BasePoint`x;
	C<I> := Parent(BPx);
	for j in [1..#IntPoints] do
		if Abs(NewPath[#NewPath]`StartPt-IntPoints[j][2]) lt X`Error then
			ArcOrient := Sign(Arg((DP[IntPoints[j][1]] - BPx) * Exp((-1)*Arg(Gamma`EndPt - BPx)*I)));
			if ArcOrient eq 0 then
				ArcOrient := -1;
			end if;
			NextArc := CArc(IntPoints[j][2],IntPoints[j][3],DP[IntPoints[j][1]]:o:=ArcOrient);
			NextLine := CLineSegment(NextArc`EndPt,Gamma`EndPt);
			Prune(~NewPath);
			NewPath cat:= [NextArc,NextLine];
		else
			NewLine := CLineSegment(NewPath[#NewPath]`StartPt,IntPoints[j][2]);
			ArcOrient := Sign(Arg((DP[IntPoints[j][1]] - BPx) * Exp((-1)*Arg(Gamma`EndPt - BPx)*I)));
			if ArcOrient eq 0 then
				ArcOrient := -1;
			end if;
			NextArc := CArc(IntPoints[j][2],IntPoints[j][3],DP[IntPoints[j][1]]:o:=ArcOrient);
			NextLine := CLineSegment(NextArc`EndPt,Gamma`EndPt);
			Prune(~NewPath);
			NewPath cat:= [NewLine,NextArc,NextLine];
		end if;
	end for;
	return NewPath;
end function;

procedure IntegrateOnSheet(Paths,EndPoint,X)
/* Integrate Paths on one sheet to EndPoint, used for the Abel-Jacobi map */
	NP := #Paths;
	CC<I> := X`ComplexFields[3];
	RR := RealField(Precision(CC));
	Cz<z> := PolynomialRing(CC);
	Cxy<x,y> := PolynomialRing(CC,2);
	CompPrec := Precision(X`ComplexFields[2]);
	Err := Real(10^-(CompPrec+1));
	f := X`ComplexDefPol;
	dfy := Derivative(f,2);
	m := X`Degree[1];
	g := X`Genus;
	
	/* Differentials */
	if X`Baker then
		DFF_Factors := [ ChangeRing(dfy,CC) ];
		DFF_Test := [ ChangeRing(Derivative(f,2),ComplexField(10)) ];
	else
		DFF_Factors := [ EmbedPolynomial(Fac,X`Embedding,Cxy) : Fac in X`HolomorphicDifferentials[1] ];
		DFF_Test := X`HolomorphicDifferentials[5];
	end if;

	vprint RS,2 : "Paths:",Paths;
	vprint RS,2 : "Integrate reversely on one sheet to y-value:",ChangePrecision(EndPoint,10);
	NewPaths := Reverse([ ReversePath(p) : p in Paths ]);
	vprint RS,2 : "New paths:",NewPaths;
	assert Distance(EndPoint,X`Fiber(Paths[#Paths]`EndPt)) lt X`WeakError;
	assert Distance(EndPoint,X`Fiber(NewPaths[1]`StartPt)) lt X`WeakError;
	/* Use Newton's method, define locally here */
	NewtonIteration := function(p,dp,x2,y1,Err)
		px2 := Evaluate(p,[x2,z]);
		dpx2 := Evaluate(dp,[x2,z]);
		repeat
			w := Evaluate(px2,y1)/Evaluate(dpx2,y1);
			y1 -:= w;
		until Abs(w) lt Err;
		return y1;
	end function;

	for k in [1..NP] do
		Gamma := NewPaths[k];
		/* Compute integration parameter */
		if X`IntMethod in ["GL","Mixed"] then
			GLCC_Params_Path(X`LPDP,Gamma,Err,"GL");
		elif X`IntMethod eq "CC" then
			GLCC_Params_Path(X`LPDP,Gamma,Err,"CC");
		else
			DE_Params_Path(X`LPDP,Gamma);
		end if;
		Gamma`Integrals := Matrix(CC,1,g,[]);
		for t in [1..#Gamma`Subpaths] do
			SGamma := Gamma`Subpaths[t];
			vprint RS,2 : "############################### Next Path: #################################";
			vprint RS,2 : "Integration subpath:",SGamma,"of length",ChangePrecision(SGamma`Length,10),"with IntPar:",SGamma`IntPar;
			SGamma`IN := Max([ l : l in [1..#X`IntSchemes[SGamma`IntMethod]] | X`IntSchemes[SGamma`IntMethod][l]`IntPar lt SGamma`IntPar ] cat [0]);
			if SGamma`IN eq 0 then
				SGamma`IN := 1;
				if X`IntMethod eq "DE" then
					r := (19/20)*RR!SGamma`IntPar;
					HeuristicBound(SGamma,DFF_Test,[r],X);
					B := Max(SGamma`Bounds);
					Insert(~X`IntSchemes["DE"],1,DE_Integration(r,CompPrec:Bounds:=[B,B]));
				else
					if SGamma`IntPar le 1+(1/50) then
						r := (1/2)*(SGamma`IntPar+1);
					else
						r := SGamma`IntPar-1/100;
					end if;
					HeuristicBound(SGamma,DFF_Test,[r],X);
					B := Max(SGamma`Bounds);
					if X`IntMethod in ["GL","Mixed"] then
						Insert(~X`IntSchemes["GL"],1,GL_Integration(r,Precision(RR),Err:Bound:=B));
					elif X`IntMethod eq "CC" then
						Insert(~X`IntSchemes["CC"],1,CC_Integration(r,Precision(RR),Err:Bound:=B));
					else
						error Error("Invalid integration method.");
					end if;
				end if;
			end if;					
			/* Get correct integration scheme & append one */
			IntSch := X`IntSchemes[SGamma`IntMethod][SGamma`IN];
			Abscissas := Append(IntSch`Abscissas,1);

			/* Integrals for subpaths */
			PathDiffVector := Matrix(CC,1,g,[]);
			vprint RS,2 : "Number of Points:",IntSch`N;
			xj, dxj := SGamma`Evaluate(Abscissas[1]);
			if k eq 1 and t eq 1 then
				yj := NewtonIteration(f,dfy,xj,EndPoint,Err);
			else
				yj := NewtonIteration(f,dfy,xj,yj,Err);
			end if;
			if Gamma`Type eq "LineSegment" then
				for j in [1..IntSch`N] do
					OneVec := X`DFFEvaluate(DFF_Factors,xj,[yj],1);
					OneVec *:= IntSch`Weights[j];
					PathDiffVector +:= OneVec;
					nxj := SGamma`Evaluate(Abscissas[j+1]);
					yj := NewtonIteration(f,dfy,nxj,yj,Err);
					xj := nxj;
				end for;
				Gamma`Integrals +:= PathDiffVector * dxj;
			else
				for j in [1..IntSch`N] do
					OneVec := X`DFFEvaluate(DFF_Factors,xj,[yj],1);
					OneVec *:= (IntSch`Weights[j] * dxj);
					PathDiffVector +:= OneVec;
					nxj, ndxj := SGamma`Evaluate(Abscissas[j+1]);
					yj := NewtonIteration(f,dfy,nxj,yj,Err);
					xj := nxj; dxj := ndxj;
				end for;
				Gamma`Integrals +:= PathDiffVector;
			end if;
		end for;
	end for;
	Paths[1]`Sheets := yj;
	for k in [1..NP] do
		Paths[k]`Integrals := -NewPaths[NP-k+1]`Integrals;
	end for;
end procedure;

intrinsic AbelJacobi( X::RieSrf, P::PlcFunElt : Reduction := "Complex", Method := "Swap" ) -> Mtrx
{ Compute the Abel-Jacobi map of the the divisors on X defined bt the function field divisor D with respect the base point of X. }
	return AbelJacobi(X,1*P:Reduction:=Reduction,Method:=Method);
end intrinsic;
intrinsic AbelJacobi( X::RieSrf, P::PlcFunElt, Q::PlcFunElt : Reduction := "Complex", Method := "Swap" ) -> Mtrx
{ Compute the Abel-Jacobi map of the the divisors on X defined bt the function field divisor D with respect the base point of X. }
	return AbelJacobi(X,1*Q-1*P:Reduction:=Reduction,Method:=Method);
end intrinsic;
intrinsic AbelJacobi( X::RieSrf, D::DivFunElt : Reduction := "Complex", Method := "Swap" ) -> Mtrx
{ Compute the Abel-Jacobi map of the the divisors on X defined bt the function field divisor D with respect the base point of X. }
	require FunctionField(X) eq FunctionField(D) : "FunctionField(D) need to be FunctionField(X).";
	require Reduction in ["None","Real","Complex"] : "Reduction has to be either None, Real or Complex";
	require Method in ["Swap","Direct"] : "Method has to be either 'Swap' or 'Direct'";
	/* Prepare reduction matrices */
	ReductionMatrix(X,Reduction);
	/* Compute support of input divisor D */
	Points, Mults := Support(D);
	/* Take care of special places */
	if not assigned X`AJM_SpecialDivisors then
		SpecialPointsByMoving(X:Method := Method);
	end if;
	SpecialPlaces := [ Dv`Place : Dv in X`AJM_SpecialDivisors ];
	FF<x,y> := FunctionField(X);
	K := ConstantField(FF);
	NewPoints := []; NewMults := [];
	C<I> := Parent(X`BasePoint`x);
	P0 := Floor(X`BasePoint`x);
	P0 := Zeros(x-P0)[1];
	/* Now build DivRieSrfElt! */
	ExtraDiv := [];
	for l in [1..#Points] do
		P := Points[l];
		if P eq P0 then
			FIBX0 := X`Fiber(X`BasePoint`x);
			for n in [1..X`Degree[1]] do
				Append(~NewPoints,X![X`BasePoint`x,FIBX0[n]]);
				Append(~NewMults,Mults[l]);
			end for;
		else
			pos := Position(SpecialPlaces,P);
			if pos ne 0 then
				Append(~ExtraDiv,<pos,Mults[l]>);
			else
				PX := Evaluate(x,P);
				PY := Evaluate(y,P);
				if PX eq 0 and PY eq 0 then
					PXFR := [ Zero(C) ]; PYFR := [ Zero(C) ];
				else
					if PX eq 0 then
						PXFR := [ Zero(C) : j in [1..Degree(P)*Degree(K)] ];
					else
						PXFR := ChangeUniverse(Conjugates(AbsoluteField(Parent(PX))!PX:Precision:=Precision(C)),C);
					end if;
					if PY eq 0 then
						PYFR := [ Zero(C) : j in [1..Degree(P)*Degree(K)] ];
					else
						PYFR := ChangeUniverse(Conjugates(AbsoluteField(Parent(PY))!PY:Precision:=Precision(C)),C);
					end if;
				end if;
				assert #PYFR eq #PXFR;
				ll := 0;
				for m in [1..#PXFR] do
					yn, Pt := IsCoercible(X,[PXFR[m],PYFR[m]]);
					if yn then
						ll +:= 1;
						Append(~NewPoints,Pt);
						Append(~NewMults,Mults[l]);
					end if;
				end for;
				assert ll eq Degree(P);
			end if;
		end if;
	end for;
	if #NewPoints eq 0 then
		ND := &+[ DD[2] * X`AJM_SpecialDivisors[DD[1]] : DD in ExtraDiv ];
	else
		ND := Divisor(NewPoints,NewMults);
		ND`AJM := AbelJacobi(ND:Reduction:="None",Method:=Method);
		for DD in ExtraDiv do
			ND +:= DD[2] * X`AJM_SpecialDivisors[DD[1]];
		end for;
	end if;
	if Reduction eq "Real" then
		return ChangeRing(PeriodLatticeReductionReal(ND`AJM,X),RealField(X`Prec));
	else
		return ChangeRing(PeriodLatticeReductionComplex(ND`AJM,X),X`ComplexFields[1]);
	end if;	
end intrinsic;
intrinsic AbelJacobi( P::RieSrfPt : Method := "Swap", Reduction := "Complex" ) -> Mtrx
{ Computes the Abel-Jacobi map of the zero divisor [ P - P_0 ] where P_0 is the base point of the Riemann surface. }
	return AbelJacobi(Divisor([P],[1]):Method:=Method,Reduction:=Reduction);
end intrinsic;
intrinsic AbelJacobi( P::RieSrfPt, Q::RieSrfPt : Method := "Swap", Reduction := "Complex" ) -> Mtrx
{ Computes the Abel-Jacobi map of the zero divisor [ Q - P ]. }
	return AbelJacobi(Divisor([P,Q],[-1,1]):Method:=Method,Reduction:=Reduction);
end intrinsic;
intrinsic AbelJacobi( D::DivRieSrfElt, P0::RieSrfPt : Method := "Swap", Reduction := "Complex" ) -> Mtrx
{ Computes the Abel-Jacobi map of the divisor D with basepoint P0. }
	return AbelJacobi(D-D`Degree*P0:Method:=Method,Reduction:=Reduction);
end intrinsic;
intrinsic AbelJacobi( D::DivRieSrfElt : Method := "Swap", Reduction := "Complex" ) -> Mtrx
{ Compute the Abel-Jacobi map of a divisor D with respect to the base point of its Riemann surface. }

	require Reduction in ["None","Real","Complex"] : "Reduction has to be either None, Real or Complex";
	require Method in ["Swap","Direct"] : "Method has to be either 'Swap' or 'Direct'";
	vprint RS,1 : "Computing Abel-Jacobi map...";
	vprint RS,2 : "Divisor:",D;
	vprint RS,2 : "Reduction:",Reduction;

	/* Riemann surface */
	X := RiemannSurface(D);

	/* Prepare reduction matrices */
	if Reduction ne "None" then
		ReductionMatrix(X,Reduction);
	end if;

	if not assigned D`AJM then
	/* Complex field and total complex integral */
	C2<I> := X`ComplexFields[2];
	C3 := X`ComplexFields[3];	

	if X`IsSuperelliptic then
		/* This is the superelliptic case! */	
		TotalComplexIntegral := Matrix(C2,X`Genus,1,[]);
		
		ComplexEdges := [];
		/* Sort out points at infinity */
		Points, Mults := Support(D);	
		for k in [1..#Points] do
			P := Points[k];
			v_P :=  Mults[k];
			vprint RS,2 : "Next point:",P;
			if not P`IsFinite then
				/* Points at infinity */
				SE_AJM_InftyPoints(X,P`Index);
				TotalComplexIntegral +:= v_P * ChangeRing(X`AJM_InfinitePoints[P`Index],C2);
			else
				/* Finite points */
				Dist, Ind := Distance(P`x,X`DiscriminantPoints);  
				TotalComplexIntegral +:= v_P * ChangeRing(X`AJM_RamificationPoints[Ind],C2);
				if Dist gt X`Error then
					NewEdge := SE_Edge(Ind,[P`x,P`y]);
					NewEdge`vp := v_P;
					EdgeData(NewEdge,X`DiscriminantPoints,[],X`Degree[1],X`Degree[2]);
					Append(~ComplexEdges,NewEdge);
				end if;
			end if;
		end for;			

		/* No integrations needed in this special case! */
		if #ComplexEdges eq 0 then
			D`AJM := TotalComplexIntegral;
		else
		/* Integration parameters */
		GJ_Params, DE_Params, GJ_Edges, DE_Edges := Mixed_Params_AJM(ComplexEdges,X);
		vprint RS,2 :"GJ_Params:",GJ_Params;
		vprint RS,2 :"DE_Params:",DE_Params;
		/* Maximal absolute value */
		MaxAbs := Max( [ P[1] : P in GJ_Params ] cat [ P[1] : P in DE_Params ]);

		/* Even more precision? */
		ExtraPrec := 2*Max(5,Ceiling(Log(10,Binomial(X`Degree[2],Floor(X`Degree[2]/4))*MaxAbs)));
		if ExtraPrec+X`Prec gt Precision(X`ComplexFields[3]) then
			vprint RS,2 :"Extra precision (AJM):",ExtraPrec;
			C3<I> := ComplexField(Precision(X`ComplexFields[3])+ExtraPrec);
			X`ComplexFields[3] := C3;
			if IsDefined(X`ComplexFields,4) and Precision(C3) gt Precision(X`ComplexFields[4]) then
				X`DiscriminantPoints := SE_DKPEB(X`DefiningPolynomial,X`DiscriminantPoints,Precision(C3));
				X`ComplexDefPol := ChangeRing(X`DefiningPolynomial,C3);
				X`ComplexFields[4] := C3;
			end if;
		end if;
	
		/* Compute integration schemes */
		SE_DE_Integration(DE_Params,X:AJM);
		SE_GJ_Integration(GJ_Params,X:AJM);

		/* Actual integrations from P_k to P */
		for CE in GJ_Edges cat DE_Edges do
			TotalComplexIntegral +:= CE`vp * Matrix(C2,X`Genus,1,SE_Integrals_Edge_AJM(CE,X));
		end for;

		D`AJM := TotalComplexIntegral;
		end if;
	else
		assert Method in ["Direct","Swap"];
		TotalComplexIntegral := Matrix(C2,1,X`Genus,[]);
		STSI := X`SheetToSheetIntegrals;
		Points, Mults := Support(D);
		for k in [1..#Points] do
			P := Points[k]; vP := Mults[k];
			vprint RS,2 : "Next Point:",P;
			if P`x cmpeq Infinity() then
				/* Points at infinity */
				s := P`Sheets[1];
				assert s in [1..X`Degree[1]];
				if not assigned X`AJM_InfinitePoints then 
					vprint RS,2 : "Heuristically computing Abel-Jacobi map to infinity using double-exponential integration...";
					AJM_DE_InfinitePoints(X);
				end if;
				Sheet2 := s^(Inverse(X`AJM_InfinitePoints`Permutation));
				TotalComplexIntegral +:= vP * ChangeRing((X`AJM_InfinitePoints`Integrals[Sheet2] + STSI[Sheet2]),C2);		
			else
				assert Type(P`x) eq FldComElt;
				/* Finite singularities and Y-infinite points */
				Dist, Ind := Distance(P`x,X`DiscriminantPoints);
				if not assigned P`y or P`y cmpeq Infinity() then
					assert Dist lt X`Error;
					assert assigned P`Sheets;
					if not IsDefined(X`AJM_DiscriminantPoints,Ind) then
						AJM_DiscriminantPoints(X,Ind);
					end if;
					ChCh := X`AJM_DiscriminantPoints[Ind];
					Sheet2 := P`Sheets[1];
					TotalComplexIntegral +:= vP * ChangeRing((ChCh`Integrals[Sheet2] + STSI[Sheet2]),C2);			
				elif P in X`CriticalPoints then 
					/* Critical points */
					assert Dist lt X`Error;
					vprint RS,2 : "Critical point!";
					vprint RS,1 : "Using method:",Method;
					if Method eq "Direct" then
						/* Abel-Jacobi map already computed? */
						if not IsDefined(X`AJM_DiscriminantPoints,Ind) then
							AJM_DiscriminantPoints(X,Ind);
						end if;
						ChCh := X`AJM_DiscriminantPoints[Ind];
						Fiber_xP := X`Fiber(P`x);
						Dist2, Sheet := Distance(P`y,Fiber_xP);
						assert Dist2 lt X`WeakError;
						//Sheet2 := Sheet^(Inverse(ChCh`Permutation));
						Sheet2 := Sheet;
						TotalComplexIntegral +:= vP * (ChCh`Integrals[Sheet2] + STSI[Sheet2]);
					elif Method eq "Swap" then
						vprint RS,2 : "Compute swapped Riemann surface!";
						SwappedSurface(X);
						Q := New(RieSrfPt); Q`RieSrf := X`SwappedSurface; Q`x := P`y; Q`y := P`x; Q`IsFinite := true;
						O := New(RieSrfPt); O`RieSrf := X`SwappedSurface; O`x := X`BasePoint`y; O`y := X`BasePoint`x; O`IsFinite := true;
						OmQ := O - Q;
						V := AbelJacobi(OmQ:Reduction:="None");
						TotalComplexIntegral +:= vP * ChangeRing(Transpose(OmQ`AJM),C2);
					else
						error Error("Unknown method.");
					end if;
				else
					assert Type(P`y) eq FldComElt;
					vprint RS,2 : "Distance to discriminant point:",ChangePrecision(Dist,10);
					vprint RS,2 : "Normal point!";
					/* Is it the base point? */
					Fiber_xP := X`Fiber(P`x);
					Dist2, Sheet := Distance(P`y,Fiber_xP);
					assert Dist2 lt X`WeakError;
					BPx := X`BasePoint`x;
					if Abs(P`x-BPx) lt X`WeakError then
						vprint RS,2 : "Base point!";
						TotalComplexIntegral +:= vP * STSI[Sheet];
					else
						/* Find nearest starting point */
						Dist, Ind := Distance(P`x,X`AJM_StartingPoints);
						/* Find suitable closed chain */
						for XCh in X`ClosedChains do
							j := Position(XCh`IndexPathList,Ind);
							if j ne 0 then
							if j eq 1 then
								PTI := [ CLineSegment(C3!BPx,C3!P`x) ];
								IntegrateOnSheet(PTI,P`y,X);
								Dist, Sheet2 := Distance(PTI[1]`Sheets,X`Fiber(BPx));
								assert Dist lt X`Error;
								TotalComplexIntegral +:= vP * (STSI[Sheet2] + ChangeRing(PTI[1]`Integrals[1],C2));
							else
								ChCh := Chain(XCh`Paths[1..j-1]);
								if Dist gt X`Error then
									PTI := FindPathOnSheet(CLineSegment(C3!ChCh`Paths[j-1]`EndPt,C3!P`x),X);
									IntegrateOnSheet(PTI,P`y,X);
									Dist, Sheet2 := Distance(PTI[1]`Sheets,X`Fiber(ChCh`Paths[j-1]`EndPt));
									Sheet2 := Sheet2^(Inverse(ChCh`Permutation));
									assert Dist lt X`Error;
									TotalComplexIntegral +:= vP * (STSI[Sheet2] + ChangeRing(ChCh`Integrals[Sheet2] + &+[ PTI[l]`Integrals[1] : l in [1..#PTI]],C2));

								else
									Sheet2 := Sheet^(Inverse(ChCh`Permutation));
									TotalComplexIntegral +:= vP * (STSI[Sheet2] + ChangeRing(ChCh`Integrals[Sheet2],C2));
								end if;
							end if;
							break;
							end if;
						end for;
					end if;
				end if;	
			end if;
			D`AJM := Transpose(TotalComplexIntegral);
		end for;
	end if;
	end if;
	if Reduction eq "None" then
		return D`AJM;
	elif Reduction eq "Real" then
		return ChangeRing(PeriodLatticeReductionReal(D`AJM,X),RealField(X`Prec));
	else
		C<I> := X`ComplexFields[1];
		return ChangeRing(PeriodLatticeReductionComplex(D`AJM,X),C);
	end if;	
end intrinsic;


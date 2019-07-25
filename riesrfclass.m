/*******************************************************************************

	Riemann surface class: type RieSrf
 
	Christian Neurohr, May 2019

*******************************************************************************/

import "infinitepoints.m": AJM_DE_InfinitePoints, SE_AJM_InftyPoints;
import "fundamentalgroup.m": SpanningTree, TreeData, Mixed_Params_Tree, InternalDiscriminantPoints;
import "periodmatrix.m": PeriodMatrix, SE_PeriodMatrix;
import "abeljacobi.m": SE_TreeMatrix, SE_RamificationPoints_AJM, AJM_DiscriminantPoints;
import "miscellaneous.m": SE_DKPEB, SE_OrdFldComElt, IsWeaklyIn, EmbedPolynomial;
import "riesrfdivpts.m": AnalyzeSpecialPoints;

declare verbose RS, 3;

/* Riemann surfaces type RieSrf defined here */
declare type RieSrf;

declare attributes RieSrf:
			IsSuperelliptic,
			DefiningPolynomial, 
			HomoDefPol,
			ComplexDefPol,
			ComplexHomoDefPol,
			Fiber, 
			Degree,
			FunctionField, 
			Genus, 
			Ordering, 
			BranchPoints,
			DiscriminantPoints,
			SafeRadii,
			LPDP,
			DFF,
			HolomorphicDifferentials, 
			ReductionMatrixReal,
			ReductionMatricesComplex,
			BasePoint, 
			PathPieces, 
			IndexPathLists, 
			Embedding,
			ClosedChains, 
			InfiniteChain,
			LocalMonodromy, 
			MonodromyGroup, 
			HomologyBasis, 
			Prec, 
			SmallPeriodMatrix,	
			BigPeriodMatrix,
			AJM_DiscriminantPoints, 
			AJM_StartingPoints,
			AJM_InfinitePoints,
			IntMethod,
			IntSchemes,
			SheetToSheetIntegrals,
			Error,
			WeakError,
			CriticalPoints,
			FiniteSingularities,
			InfinitePoints,
			InfiniteSingularities,
			SingularPoints,
			SwappedSurface,
			CriticalValues,
			ComplexFields,
			Bounds,
			LeadingCoeff,
			Zetas,
			DifferentialChangeMatrix,
			SpanningTree,
			ElementaryIntegrals,
			IntersectionMatrix,
			TreeMatrix,
			AJM_RamificationPoints,
			AJM_SumOfInftyPoints,
			AJM_SpecialDivisors,
			YInfinitePoints,
			Baker,
			DFFEvaluate,
			RamificationPoints,
			InftyCoords,
			AffineModel;

/* Printing */
intrinsic Print( X::RieSrf )
{ Print the Riemann surface X. }
	if X`IsSuperelliptic then
		print "Superelliptic Riemann surface of genus",X`Genus ,"defined as degree",X`Degree[1],"covering defined by",X`DefiningPolynomial,"and prescribed precision",X`Prec;
	else
		print "Riemann surface of genus", X`Genus ,"defined by: 0 =",X`DefiningPolynomial,"and prescribed precision",X`Prec;
	end if;
	print "";
	print "Computed data:";
	print " Complex fields:",[Precision(X`ComplexFields[k]):k in [1..#X`ComplexFields]];
	print " Discriminant points:", assigned X`DiscriminantPoints;
	print " BasePoint:", X`BasePoint;
	print " Path pieces:", assigned X`PathPieces;
	print " Index path lists:", assigned X`IndexPathLists;
	print " Closed chains:", assigned X`ClosedChains;
	print " Branch points:", assigned X`BranchPoints;
	print " Local monodromy:", assigned X`LocalMonodromy;
	print " Monodromy group:", assigned X`MonodromyGroup;
	print " Homology basis:", assigned X`HomologyBasis;
	print " Holomorphic differential:", assigned X`HolomorphicDifferentials;
	print " Integration method:", X`IntMethod;
	print " BigPeriod matrix:",assigned X`BigPeriodMatrix;
	print " SmallPeriod matrix:",assigned X`SmallPeriodMatrix;
	print " Reduction matrix (real)",assigned X`ReductionMatrixReal;
	print " Reduction matrices (complex)",assigned X`ReductionMatricesComplex;
	print " SheetToSheetIntegrals:", assigned X`SheetToSheetIntegrals;
end intrinsic;

intrinsic 'eq'(X::RieSrf,Y::RieSrf) -> BoolElt
{ Equality for Riemann surfaces. }
	if X`Prec ne Y`Prec then
		return false;
	end if;
	if X`IsSuperelliptic then
		C := X`ComplexFields[1];
		return (ChangeRing(X`DefiningPolynomial,C) eq ChangeRing(Y`DefiningPolynomial,C)) and (X`Degree[1] eq Y`Degree[1]);
	else
		return (X`DefiningPolynomial eq Y`DefiningPolynomial) and (X`Embedding eq Y`Embedding);
	end if; 
end intrinsic;

intrinsic RiemannSurface( f::RngMPolElt : Precision := 30, IntMethod := "Mixed" ) -> RieSrf
{ Create a Riemann surface object defined by f(x,y) = 0 over the rationals. }
	vprint RS,1 : "Defining polynomial over the rationals:",f;
	K := BaseRing(Parent(f));
	require K eq Rationals() : "Polynomial has to be defined over the rationals.";
	K := RationalsAsNumberField();
	f := ChangeRing(f,K);
	sigma := InfinitePlaces(K)[1];
	return RiemannSurface(f,sigma:IntMethod:=IntMethod,Precision:=Precision); 
end intrinsic;
intrinsic RiemannSurface( f::RngMPolElt, sigma::PlcNumElt : Precision := 30, IntMethod := "Mixed" ) -> RieSrf
{ Create a Riemann surface object defined by f(x,y) = 0 over a number field using the embedding sigma. }

	/* Requirements and K[x,y] */
	Kxy<x,y> := Parent(f);
	require Rank(Kxy) eq 2 : "Input has to be a polynomial in two variables.";
	K := BaseRing(Kxy);
	require Type(K) eq FldNum : "Polynomial has to be defined over a number field.";
	require IsInfinite(sigma) : "PlcNumElt has to be infinite";
	vprint RS,1 : "Defining polynomial: ",f;
	vprint RS,1 : "defined over:",K;
	vprint RS,1 : "with embedding:",sigma;
	require IntMethod in ["DE","GL","CC","Mixed"] : "Undefined integration method.";

	/* Create object */
	X := New(RieSrf);	

	/* Created Riemann surface not considered superelliptic */
	X`IsSuperelliptic := false;
	
	/* Precision & complex field */
	X`Prec := Max(Precision,30);
	vprint RS,1 : "Precision:",X`Prec;
	X`ComplexFields := [ ComplexField(X`Prec) ];

	/* Error control */
	X`WeakError := Real(10^-((2/3)*X`Prec));
	X`Error := Real(10^-(X`Prec+1));

	/* Ordering of sheets */
	X`Ordering := function(x,y)
		if Abs(Re(x)-Re(y)) gt X`Error then
			if Re(x) lt Re(y) then 
				return -1;
			elif Re(x) gt Re(y) then 
				return 1;
			end if;
		elif Abs(Im(x)-Im(y)) gt X`Error then
			if Im(x) lt Im(y) then 
				return -1;
			elif Im(x) gt Im(y) then 
				return 1; 
			end if; 
		else
			return 0;
		end if;
	end function;

	/* Complex embedding */
	X`Embedding := sigma;

	/* Save defining polynomial */
	X`DefiningPolynomial := f;

	/* Degrees */
	X`Degree := [Degree(X`DefiningPolynomial,2),Degree(X`DefiningPolynomial,1)];	

	/* Function field and genus */
	//FF<x,y> := FunctionField(f:SeparatingElement:=Parent(f).2);
	FF<x,y> := FunctionField(f);
	X`FunctionField := FF;
	X`DFF := BasisOfDifferentialsFirstKind(FF);
	vprint RS,2 : "Holomorphic differentials:",X`DFF;
	X`Genus := #X`DFF;
	mg := X`Degree[1] * X`Genus;

	/* Throw in some extra precision */
	CompPrec := X`Prec + X`Degree[1] + 3;
	Append(~X`ComplexFields,ComplexField(CompPrec));

	/* Holomorphic differentials */
	InnerFaces := [];
	NP := NewtonPolygon(f:Faces:="All");
	dm3 := Degree(f)-3;
	for i in [0..dm3] do
		for j in [0..dm3-i] do
			if IsInterior(NP,<i+1,j+1>) then
				Append(~InnerFaces,[i+1,j+1]);
			end if;
		end for;
	end for;
	vprint RS,1 : "Genus:",X`Genus;
	vprint RS,1 : "#InnerFaces:",#InnerFaces;
	//InnerFaces := [];
	if X`Genus ne #InnerFaces then
		X`Baker := false;
		dx := Differential(X`FunctionField.1);
		/*if Degree(f,1) gt Degree(f,2) then
			vprint RS,1 : "Integrate w.r.t dx";
			dx := Differential(X`FunctionField.1);  // dx
		else
			vprint RS,1 : "Integrate w.r.t dy";
			dx := Differential(X`FunctionField.2);  // dy
		end if;*/
		PRs := []; Pows := []; DFF_Factors := {};
		for j in [1..X`Genus] do
			PR,Pow := ProductRepresentation(X`DFF[j]/dx);
			Append(~PRs,PR); Append(~Pows,Pow);
			DFF_Factors join:= SequenceToSet(PR);
		end for;
		DFF_Factors := SetToSequence(DFF_Factors); NrFac := #DFF_Factors;
		DFF_Powers := Matrix(Integers(),NrFac,X`Genus,[]);
		for j in [1..X`Genus] do
			PR := PRs[j];
			for k in [1..#PR] do
				NextInd := Position(DFF_Factors,PR[k]);
				if NextInd ne 0 then
					DFF_Powers[NextInd][j] := Pows[j][k];
				end if;
			end for;
		end for;
		print "DFF_Factors:",DFF_Factors;
		DFF_Factors := [ Numerator(RationalFunction(Fac,K)) : Fac in DFF_Factors ];
		/*if X`Degree[1] ge X`Degree[2] then
			DFF_Factors := [ Evaluate(Fac,[Parent(Fac).2,Parent(Fac).1]) : Fac in DFF_Factors ];
			X`AffineModel := Evaluate(f,[Kxy.2,Kxy.1]);
			NewFac := RationalFunction(dx/Differential(X`FunctionField.1),K);
			Append(~DFF_Factors,Numerator(NewFac));
			Append(~DFF_Factors,Denominator(NewFac));
			DFF_Powers := VerticalJoin(DFF_Powers,Matrix(Integers(),1,X`Genus,[1 : j in [1..X`Genus]]));
			DFF_Powers := VerticalJoin(DFF_Powers,Matrix(Integers(),1,X`Genus,[-1 : j in [1..X`Genus]]));
		else
			X`AffineModel := f;
		end if;
		NrFac := #DFF_Factors;*/
		//DFF_Factors := [ Numerator(Fac) : Fac in DFF_Factors ];
		vprint RS,2 : "DFF_Factors:",DFF_Factors;
		vprint RS,2 : "DFF_Powers:",DFF_Powers;
		MinPows := [ Min( [DFF_Powers[j][k] : k in [1..X`Genus]]) : j in [1..NrFac] ];
		MaxPows := [ Max([DFF_Powers[j][k] : k in [1..X`Genus]])-MinPows[j] : j in [1..NrFac] ];
		
		/* Low precision differentials */
		C_10xy := PolynomialRing(ComplexField(10),2);
		//DFF_Factors_Test := [ EmbedPolynomial(Numerator(Fac),X`Embedding,C_10xy) : Fac in DFF_Factors ];
		DFF_Factors_Test := [ EmbedPolynomial(Fac,X`Embedding,C_10xy) : Fac in DFF_Factors ];
		vprint RS,2 : "Complex DFF_Factors:",DFF_Factors_Test;
		/* Product representation of differentials */
		X`HolomorphicDifferentials := <DFF_Factors,DFF_Powers,MinPows,MaxPows,DFF_Factors_Test>;
		X`DFFEvaluate := function(Facs,xj,yj,m)
			CC := BaseRing(Universe(Facs));
			OneMat := Matrix(CC,m,X`Genus,[ 1 : j in [1..m*X`Genus]]);
			for l in [1..NrFac] do
				Fac_x := Evaluate(Facs[l],[xj,PolynomialRing(CC).1]);
				for s in [1..m] do
					val := Evaluate(Fac_x,yj[s]);
					Fac_xys := [ val^MinPows[l] ];
					for k in [1..MaxPows[l]] do
						Append(~Fac_xys,Fac_xys[k]*val);
					end for;
					for k in [1..X`Genus] do
						OneMat[s][k] *:= Fac_xys[DFF_Powers[l][k]-MinPows[l]+1];
					end for;
				end for;
			end for;
			return OneMat;
		end function;
	else
		X`Baker := true;
		mi := Max([ s[1] : s in InnerFaces ]);
		mj := Max([ s[2] : s in InnerFaces ]);
		X`HolomorphicDifferentials := < InnerFaces, Derivative(X`DefiningPolynomial,2) >;
		vprint RS,2 : "InnerFaces:",InnerFaces;
		X`DFFEvaluate := function(Facs,xj,yj,m)
			CC := BaseRing(Universe(Facs));
			OneMat := Matrix(CC,m,X`Genus,[]);
			dfyx := Evaluate(Facs[1],[xj,PolynomialRing(CC).1]);
			Vec := DiagonalMatrix(CC,[ 1/Evaluate(dfyx,yj[s]) : s in [1..m] ]);
			px := [ 1, xj ];
			for l in [2..mi] do
				Append(~px,px[l]*xj);
			end for;
			for s in [1..m] do
				pys := [ 1, yj[s] ];
				for l in [2..mj] do
					Append(~pys,pys[l]*yj[s]);
				end for;
				for l in [1..X`Genus] do
					OneMat[s][l] := px[InnerFaces[l][1]] * pys[InnerFaces[l][2]];
				end for;
			end for;
			return Vec * OneMat;
		end function;
	end if;
	vprint RS,1 : "Using Baker-basis?:",X`Baker;

	/* Homogenization */
	Kxyz := PolynomialRing(K,3);
	X`HomoDefPol := Homogenization(Evaluate(X`DefiningPolynomial,[Kxyz.1,Kxyz.2]),Kxyz.3);
	//X`HomoDefPol := Homogenization(Evaluate(X`AffineModel,[Kxyz.1,Kxyz.2]),Kxyz.3);

	/* Arrays for integration */
	vprint RS,1 : "IntMethod:",IntMethod;
	X`IntMethod := IntMethod;
	X`IntSchemes := AssociativeArray();
	X`IntSchemes["GL"] := [];
	X`IntSchemes["CC"] := [];
	X`IntSchemes["DE"] := [];

	/* Compute discriminant points */
	DP, X`Bounds, BYValues := InternalDiscriminantPoints(X);
	vprint RS,1 : "#Discriminant points:",#DP;

	/* Compute fundamental group */
	X`BasePoint, X`DiscriminantPoints, X`PathPieces, X`IndexPathLists, X`SafeRadii := FundamentalGroup(DP:BasePoint := "Left");
	vprint RS,1 : "BasePoint:",ChangePrecision(X`BasePoint,10);
	vprint RS,1 : "Universe of discriminant points:",Universe(X`DiscriminantPoints);
	vprint RS,1 : "Discriminant points:",ChangeUniverse(X`DiscriminantPoints,ComplexField(10));

	/* Low precision discriminant points */
	X`LPDP := ChangeUniverse(X`DiscriminantPoints,ComplexField(30));
	print "X`LPDP:",X`LPDP;
	/* Save complex model of maximal precision */
	C<I> := Parent(X`BasePoint);
	Cz<z> := PolynomialRing(C);
	Cxy<x,y> := PolynomialRing(C,2);
	X`ComplexDefPol := EmbedPolynomial(X`DefiningPolynomial,X`Embedding,Cxy);
	//X`ComplexDefPol := EmbedPolynomial(X`AffineModel,X`Embedding,Cxy);
	CXYZ<xx,yy,zz> := PolynomialRing(C,3);
	X`ComplexHomoDefPol := Homogenization(Evaluate(X`ComplexDefPol,[xx,yy]),zz);

	/* Fiber function */
	X`Fiber := function(x0)
		fx0 := Evaluate(X`ComplexDefPol,[C!x0,z]);
		Cfx0 := Coefficients(fx0);
		for k in [1..Degree(fx0)+1] do
			if Abs(Cfx0[k]) lt X`Error then
				Cfx0[k] := Zero(C);
			end if;
		end for;
		fx0 := Cz!Cfx0;
		dfx0 := Degree(fx0);
		if dfx0 lt X`Degree[1] then
		//if dfx0 lt Degree(X`AffineModel,2) then
			vprint RS,2 : "Careful: Fiber contains y-infinite points!";
			if dfx0 eq 0 then
				return [];
			end if;
		end if;
		fx0 *:= 1/LeadingCoefficient(fx0);
		MRoots := RootsNonExact(fx0);
		NRoots := [];
		for k in [1..dfx0] do
			Rt := MRoots[k];
			if Abs(Re(Rt)) lt X`WeakError then
				MRoots[k] := C.1 * Im(Rt);
			end if;
			if Abs(Im(Rt)) lt X`WeakError then
				MRoots[k] := Re(Rt);
			end if;
		end for;
		/* Identify roots that are close */
		NRoots := [ MRoots[1] ];
		for k in [2..dfx0] do
			Rt := MRoots[k];
			Dist,Ind := Distance(Rt,NRoots);
			if Dist gt X`WeakError then
				Append(~NRoots,Rt);
			else
				Append(~NRoots,NRoots[Ind]);
			end if;
		end for;
		assert #NRoots eq Degree(fx0);
		Sort(~NRoots,X`Ordering);
		return NRoots;
	end function;

	/* Compute big period matrix */
	PeriodMatrix(X);
	vprint RS,1 : "Big period matrix computed:",true;

	/* BasePoint for Abel-Jacobi map */
	Pt := New(RieSrfPt); Pt`RieSrf := X; Pt`x := X`BasePoint;
	Pt`Index := 1; Pt`Sheets := {@ 1 @};
	Pt`IsFinite := true;
	Pt`y := X`Fiber(Pt`x)[1]; Pt`XYZ := [Pt`x,Pt`y,1];
	X`BasePoint := Pt;
	vprint RS,1 : "BasePoint(AJM):",X`BasePoint;

	/* Array for chains into discriminant points */
	X`AJM_DiscriminantPoints := [];

	/* Analyze special points on X */
	AnalyzeSpecialPoints(X);
	vprint RS,1 : "Infinite points:",X`InfinitePoints;
	vprint RS,1 : "Y-Infinite points:",X`YInfinitePoints;
	vprint RS,2 : "Singular points:",X`SingularPoints;

	/* Starting points of path pieces */
	X`AJM_StartingPoints := [ Gamma`StartPt : Gamma in X`PathPieces ];

	return X;
end intrinsic;

procedure SwappedSurface( X )
/* Compute the Riemann surface obtained from switchting variables x & y */
	assert X`IsSuperelliptic eq false;
	if not assigned X`SwappedSurface then
		SX := New(RieSrf);
		SX`IsSuperelliptic := X`IsSuperelliptic;
		SX`Embedding := X`Embedding;
		SX`Genus := X`Genus;
		SX`Prec := X`Prec;
		SX`Error := X`Error;
		SX`Ordering := X`Ordering;
		SX`WeakError := X`WeakError;
		SX`ComplexFields := X`ComplexFields[1..2];
		SX`IntMethod := X`IntMethod;
		SX`IntSchemes := AssociativeArray();
		SX`IntSchemes["GL"] := [];
		SX`IntSchemes["CC"] := [];
		SX`IntSchemes["DE"] := [];
		f := DefiningPolynomial(X);
		Kxy := Parent(f);
		K := BaseRing(Kxy);
		SX`DefiningPolynomial := Evaluate(f,[Kxy.2,Kxy.1]);
		Kxyz := PolynomialRing(K,3);
		SX`HomoDefPol := Homogenization(Evaluate(SX`DefiningPolynomial,[Kxyz.1,Kxyz.2]),Kxyz.3);
		SX`Degree := Reverse(X`Degree);
		SX`FunctionField := FunctionField(X);
		FF<x,y> := FunctionField(X);
		/* Update Differentials */
		SX`Baker := X`Baker;
		if SX`Baker then
			DFF := X`HolomorphicDifferentials;
			InnerFaces := [ [s[2],s[1]] : s in DFF[1] ];
			mi := Max([ s[1] : s in InnerFaces ]);
			mj := Max([ s[2] : s in InnerFaces ]);
			SX`HolomorphicDifferentials := < InnerFaces, Derivative(SX`DefiningPolynomial,2) >;
			SX`DFFEvaluate := function(Facs,xj,yj,m)
				CC := BaseRing(Universe(Facs));
				OneMat := Matrix(CC,m,SX`Genus,[]);
				dfyx := Evaluate(Facs[1],[xj,PolynomialRing(CC).1]);
				Vec := DiagonalMatrix(CC,[ 1/Evaluate(dfyx,yj[s]) : s in [1..m] ]);
				px := [ 1, xj ];
				for l in [2..mi] do
					Append(~px,px[l]*xj);
				end for;
				for s in [1..m] do
					pys := [ 1, yj[s] ];
					for l in [2..mj] do
						Append(~pys,pys[l]*yj[s]);
					end for;
					for l in [1..SX`Genus] do
						OneMat[s][l] := px[InnerFaces[l][1]] * pys[InnerFaces[l][2]];
					end for;
				end for;
				return Vec * OneMat;
			end function;
		else
			SX`DFF := X`DFF;
			FF<x,y> := FunctionField(X);
			dx := Differential(x);
			dy := Differential(y);
			PRs := []; Pows := []; DFF_Factors := {};
			dfy := Evaluate(Derivative(f,2),[x,y]);
			dfx := Evaluate(Derivative(f,1),[x,y]);
			dfydfx := dfy/dfx;
			for j in [1..SX`Genus] do
				PR,Pow := ProductRepresentation(SX`DFF[j]/dx);
				b := &*[ PR[k]^Pow[k] : k in [1..#PR] ] * dfydfx;
				rb := RationalFunction(b,K);
				nrb := Numerator(rb);
				nrb_fac := Factorization(nrb);
				if #nrb_fac gt 0 then
					lc := nrb/&*[ fac[1]^fac[2] : fac in nrb_fac ];
					drb := Denominator(rb)/lc;
					Append(~PRs,[ fac[1] : fac in nrb_fac ] cat [ drb ]); 
					Append(~Pows,[ fac[2] : fac in nrb_fac ] cat [ -1 ]);
					DFF_Factors join:= Set([ fac[1] : fac in nrb_fac ] cat [drb]);
				else
					drb := Denominator(rb)/nrb;
					Append(~PRs,[ 1,drb ]); 
					Append(~Pows,[ 1,-1 ]);
					DFF_Factors join:= { 1, drb };
				end if;
			end for;
			DFF_Factors := SetToSequence(DFF_Factors); 
			NrFac := #DFF_Factors;
			DFF_Powers := Matrix(Integers(),NrFac,SX`Genus,[]);
			for j in [1..X`Genus] do
				PR := PRs[j];
				for k in [1..#PR] do
					NextInd := Position(DFF_Factors,PR[k]);
					if NextInd ne 0 then
						DFF_Powers[NextInd][j] := Pows[j][k];
					end if;
				end for;
			end for;
			DFF_Factors := [ Evaluate(Fac,[Parent(Fac).2,Parent(Fac).1]) : Fac in DFF_Factors ];
			NrFac := #DFF_Factors;
			MinPows := [ Min( [DFF_Powers[j][k] : k in [1..X`Genus]]) : j in [1..NrFac] ];
			MaxPows := [ Max( [DFF_Powers[j][k] : k in [1..X`Genus]])-MinPows[j] : j in [1..NrFac] ];
			C_10xy := PolynomialRing(ComplexField(10),2);
			DFF_Factors_Test := [ EmbedPolynomial(Numerator(Fac),X`Embedding,C_10xy) : Fac in DFF_Factors ];
			SX`HolomorphicDifferentials := <DFF_Factors,DFF_Powers,MinPows,MaxPows,DFF_Factors_Test>;
			SX`DFFEvaluate := function(Facs,xj,yj,m)
				CC := BaseRing(Universe(Facs));
				OneMat := Matrix(CC,m,SX`Genus,[ 1 : j in [1..m*SX`Genus]]);
				for l in [1..NrFac] do
					Fac_x := Evaluate(Facs[l],[xj,PolynomialRing(CC).1]);
					for s in [1..m] do
						val := Evaluate(Fac_x,yj[s]);
						Fac_xys := [ val^MinPows[l] ];
						for k in [1..MaxPows[l]] do
							Append(~Fac_xys,Fac_xys[k]*val);
						end for;
						for k in [1..SX`Genus] do
							OneMat[s][k] *:= Fac_xys[DFF_Powers[l][k]-MinPows[l]+1];
						end for;
					end for;
				end for;
				return OneMat;
			end function;
		end if;
		DP, SX`Bounds, BYValues := InternalDiscriminantPoints(SX);
		SX`BasePoint, SX`DiscriminantPoints, SX`PathPieces, SX`IndexPathLists, SX`SafeRadii := FundamentalGroup(DP:BasePoint := "Left");
		SX`LPDP := ChangeUniverse(SX`DiscriminantPoints,ComplexField(30));
		C<I> := Parent(SX`BasePoint);
		Cz<z> := PolynomialRing(C);
		Cxy<x,y> := PolynomialRing(C,2);
		SX`ComplexDefPol := EmbedPolynomial(SX`DefiningPolynomial,SX`Embedding,Cxy);
		CXYZ<xx,yy,zz> := PolynomialRing(C,3);
		SX`ComplexHomoDefPol := Homogenization(Evaluate(SX`ComplexDefPol,[xx,yy]),zz);
		SX`Fiber := function(x0)
			fx0 := Evaluate(SX`ComplexDefPol,[C!x0,z]);
			dfx0 := Degree(fx0);
			if dfx0 lt SX`Degree[1] then
				vprint RS,2 : "Careful: Fiber contains y-infinite points!";
				if dfx0 eq 0 then
					return [];
				end if;
			end if;
			fx0 *:= 1/LeadingCoefficient(fx0);
			MRoots := RootsNonExact(fx0);
			NRoots := [];
			for k in [1..dfx0] do
				Rt := MRoots[k];
				if Abs(Re(Rt)) lt SX`WeakError then
					MRoots[k] := C.1 * Im(Rt);
				end if;
				if Abs(Im(Rt)) lt SX`WeakError then
					MRoots[k] := Re(Rt);
				end if;
			end for;
			NRoots := [ MRoots[1] ];
			for k in [2..dfx0] do
				Rt := MRoots[k];
				Dist,Ind := Distance(Rt,NRoots);
				if Dist gt SX`WeakError then
					Append(~NRoots,Rt);
				else
					Append(~NRoots,NRoots[Ind]);
				end if;
			end for;
			assert #NRoots eq Degree(fx0);
			Sort(~NRoots,SX`Ordering);
			return NRoots;
		end function;
		PeriodMatrix(SX);
		Pt := New(RieSrfPt); Pt`RieSrf := SX; Pt`x := SX`BasePoint;
		Pt`Index := 1; Pt`Sheets := {@ 1 @};
		Pt`IsFinite := true;
		Pt`y := SX`Fiber(Pt`x)[1]; Pt`XYZ := [Pt`x,Pt`y,1];
		SX`BasePoint := Pt;
		SX`AJM_DiscriminantPoints := [];
		AnalyzeSpecialPoints(SX);
		SX`AJM_StartingPoints := [ Gamma`StartPt : Gamma in SX`PathPieces ];
		SX`SwappedSurface := X;
		X`SwappedSurface := SX;	
	end if;
end procedure;


/* Constructor via univariate polynomial and degree */
intrinsic RiemannSurface( p::RngUPolElt, m::RngIntElt : Precision := 30, IntMethod := "Mixed" ) -> RieSrf
{ Creates an superelliptic Riemann surface object with defining equation y^m = p(x). }

	/* Create Riemann surface object */
	X := New(RieSrf);	
	/* It's a superelliptic Riemann surface! */
	X`IsSuperelliptic := true;
	/* Defining polynomial */
	X`DefiningPolynomial := p;
	vprint RS,1 : "DefiningPolynomial:",p; 	
	vprint RS,1 : "Degree m:",m;

	/* Precision & complex fields */
	Prec := Precision;
	_, Precision := IsIntrinsic("Precision");
	K := BaseRing(Parent(p));
	vprint RS,1 : "Field of definition:",K;
	if not IsExact(K) then
		require Precision(K) ge 30 : "Please enter polynomial with at least 30 digits precision or as polynomial over the rationals.";
		Prec := Precision(K);
	else
		require K eq Rationals() : "Please enter a polynomial defined over \Q,\R or \C.";
		if Prec lt 30 then
			Prec := 30;
			print "Precision has been increased to 30 decimal digits.";
		end if;
	end if;
	X`Prec := Max(Prec,30);
	X`ComplexFields := [ ComplexField(X`Prec) ];
	vprint RS,1 : "Precision:",Prec; 
	
	/* Degrees and genus */
	n := Degree(p); delta := Gcd(m,n);
	g := Round((1/2) * ((m-1)*(n-1) - delta + 1));
	X`Degree := [m,n,delta];
	X`Genus := g;

	/* Requirements */
	require &and[m ge 2, n ge 3] : "Degrees not supported."; 

	/* Integration method */
	require IntMethod in ["Mixed","DE","GJ"] : "Invalid integration method.";
	X`IntMethod := IntMethod;
	X`IntSchemes := AssociativeArray();
	X`IntSchemes["GJ"] := [];
	X`IntSchemes["DE"] := [];

	/* Errors */
	X`Error := 10^-(Prec+1);
	X`WeakError := Real(10^-((2/3)*X`Prec));

	/* Estimate minimal precision */
	fmonic := p/LeadingCoefficient(p);
	CoeffAbs := [ Abs(c):c in Prune(Coefficients(fmonic)) | c ne 0 ]; 
	/* Upper bound for roots */
	MaxCH := Ceiling(Max([Log(10,1+c) : c in CoeffAbs ]));
	MinCH := Abs(Floor(Log(10,Min(CoeffAbs))));
	MinPrec := Prec + Max(MaxCH,MinCH);
	vprint RS,2 : "MaxCH:",MaxCH;
	vprint RS,2 : "MinCH:",MinCH;
	vprint RS,1 : "Minimal precision:",MinPrec;
	
	/* Compute branch points */
	Points := Roots(ChangeRing(p,ComplexField(MinPrec)));
	Points := [ R[1] : R in Points ];
	require #Points eq n : "Defining polynomial has to be separable.";

	/* Fix an ordering of the branch points */
	X`Ordering := function(x,y)
		if Abs(Re(x)-Re(y)) gt X`Error then
			if Re(x) lt Re(y) then 
				return -1;
			elif Re(x) gt Re(y) then 
				return 1;
			end if;
		elif Abs(Im(x)-Im(y)) gt X`Error then
			if Im(x) lt Im(y) then 
				return -1;
			elif Im(x) gt Im(y) then 
				return 1; 
			end if; 
		else
			return 0;
		end if;
	end function;

	/* Sort branch points */
	Sort(~Points,X`Ordering);
	/* Low precision branch points */
	X`LPDP := ChangeUniverse(Points,ComplexField(30));

	/* Increased internal precision */
	CompPrec := Prec + m + 3;
	Append(~X`ComplexFields,ComplexField(CompPrec));
	vprint RS,1 : "Computational precision:",CompPrec;

	/* Compute spanning tree */
	SpanningTree(X);
	
	/* Compute integration parameters */
	Mixed_Params_Tree(X);
	vprint RS,2 : "DE_Parameters(tree):",X`SpanningTree`DE_Params;
	vprint RS,2 : "GJ_Parameters(tree):",X`SpanningTree`GJ_Params;

	/* Maximal absolute value */
	MaxAbs := Max([ P[1] : P in X`SpanningTree`GJ_Params ] cat [ P[1] : P in X`SpanningTree`DE_Params ]);

	/* Extra precision */
	ExtraPrec := Max(10,Ceiling(Log(10,Binomial(n,Floor(n/4))*MaxAbs)));
	vprint RS,1 : "Extra precision:",ExtraPrec; 	

	/* Complex field of maximal precision */
	MaxPrec := Max(MinPrec,CompPrec+ExtraPrec);
	vprint RS,1 : "Maximal precision:",MaxPrec;
	C<I> := ComplexField(MaxPrec);
	Append(~X`ComplexFields,C); 
	vprint RS,1 : "ComplexFields:",X`ComplexFields;	

	/* Branch point to maximal precision */
	if MaxPrec gt MinPrec then
		Points := SE_DKPEB(p,Points,MaxPrec);
	end if;

	/* Clean up */
	CPoints := [ C | ];
	for k in [1..n] do
		xk := Points[k];
		if Abs(Re(xk)) lt X`Error then
			xk := I*Im(xk); 
		end if;
		if Abs(Im(xk)) lt X`Error then
			xk := C!Re(xk);
		end if;
		Append(~CPoints,xk);
	end for;
	
	/* Embed univariate Polynomial */
	X`ComplexDefPol := ChangeRing(p,C);

	/* Leading coefficient */
	X`LeadingCoeff := LeadingCoefficient(X`ComplexDefPol);
	vprint RS,2 : "Leading coefficient:",ChangePrecision(X`LeadingCoeff,10); 	

	/* Holomorphic differentials: DFF = [ min_j, #j's, [ max_ij : j in [min_j..max_j] ], [ jPows ] ] */
	jm := Max(1,Ceiling((m+delta)/n));
	DF := []; jPows := []; j := jm;
	while j lt m do
		k := Floor((j*n-delta)/m);
		if k le n-1 then
			Append(~DF,k);
			jPows cat:= [ j : l in [1..k] ];
			j +:= 1;
		else
			break;
		end if;
	end while;
	DFF := <jm, #DF, DF, jPows>;
	X`HolomorphicDifferentials := DFF;

	/* Change due to leading coefficient transformations */
	LLC1 := -(1/m)*Log(X`LeadingCoeff);
	X`DifferentialChangeMatrix := [ Exp( DFF[4][k] * LLC1 ) : k in [1..X`Genus] ];

	/* Branch points, discriminant points, critical points */
	X`DiscriminantPoints := CPoints;
	X`CriticalPoints := [ ];
	for k in [1..n] do
		Pt := New(RieSrfPt); Pt`RieSrf := X; Pt`x := X`DiscriminantPoints[k];
		Pt`RamIndex := m; Pt`IsFinite := true;
		Pt`y := Zero(C); Pt`XYZ := [Pt`x,Pt`y,1];
		Append(~X`CriticalPoints,Pt);
	end for;
	X`BranchPoints := < xk : xk in X`DiscriminantPoints >;
	if X`Degree[3] ne X`Degree[1] then
		Append(~X`BranchPoints,Infinity());
	end if;

	/* Root of unity powers */
	X`Zetas := [ 1, Exp(Pi(C)*I/m) ];
	for k in [2..2*m-1] do
		Append(~X`Zetas,X`Zetas[k]*X`Zetas[2]);
	end for;

	/* Fiber function */
	X`Fiber := function(x0)
		if Distance(x0,X`DiscriminantPoints) lt X`Error then
			y := 0;
		else
			fx0 := X`LeadingCoeff * &*[ (x0-P) : P in X`DiscriminantPoints ];
			if m eq 2 then
				y := Sqrt(fx0);
			else
				y := Exp((1/m)*Log(fx0));
			end if;
		end if;
		return [ X`Zetas[2*k-1]*y : k in [1..m] ];
	end function;

	/* Compute spanning tree */
	TreeData(~X`SpanningTree,X`DiscriminantPoints,X`Zetas,m);

	/* Compute big period matrix */
	SE_PeriodMatrix(X);

	/* Analyze special points on X */
	AnalyzeSpecialPoints(X);

	/* Delete integration schemes from period matrix computation */
	X`IntSchemes["GJ"] := [];
	X`IntSchemes["DE"] := [];

	/* Compute 'map' of the spanning tree */
	SE_TreeMatrix(X);

	/* Compute Abel-Jacobi map between P_0 and other ramification points and sum of infinite points */
	SE_RamificationPoints_AJM(X);

	/* BasePoint for Abel-Jacobi map */
	X`BasePoint := X`CriticalPoints[1];

	/* Array for Abel-Jacobi map between P_0 and P_{\infty}, will be computed when needed */
	X`AJM_InfinitePoints := [];

	return X;
end intrinsic;


/* Constructor via branch points, degree (and leading coefficient) */
intrinsic RiemannSurface( L::SeqEnum[FldComElt], m::RngIntElt : IntMethod := "Mixed" ) -> RieSrf
{ Creates a superelliptic Riemann surface object with defining equation y^m = L[#L] * \prod_(i = 1)^(#L-1) (x-L[i]). }
	Cx<x> := PolynomialRing(Universe(L));
	p := L[#L] * &*[ (x - L[i]) : i in [1..#L-1] ];
	return RiemannSurface(p,m:IntMethod:=IntMethod);
end intrinsic; 


/* Access functions */
intrinsic InfinitePoints(X::RieSrf) -> SeqEnum[RieSrfPt]
{ Returns a list of infinite points on the Riemann surface X. }
	if not assigned X`InfinitePoints then
		AnalyzeSpecialPoints(X);
	end if;
	return X`InfinitePoints cat X`YInfinitePoints;
end intrinsic;
intrinsic Genus(X::RieSrf) -> RngIntElt
{ Return the genus of the Riemann surface X. }
	return X`Genus;
end intrinsic;
intrinsic Precision(X::RieSrf) -> RngIntElt
{ Returns the precision of the Riemann surface X. }
	return X`Prec;
end intrinsic;
intrinsic DefiningPolynomial(X::RieSrf) -> RngMPolElt
{ Returns the defining polynomial of the Riemann Surface X. }
	return X`DefiningPolynomial;
end intrinsic;
intrinsic ComplexPolynomial(X::RieSrf) -> RngMPolElt
{ Returns the defining polynomial of the Riemann Surface X embedded into the complex. }
	return X`ComplexDefPol;
end intrinsic;
intrinsic Embedding(X::RieSrf) -> PlcNumElt
{ Returns the complex embedding used to the define the Riemann Surface X. }
	return X`Embedding;
end intrinsic;
intrinsic HomogeneousPolynomial(X::RieSrf) -> RngMPolElt
{ Returns the homogenization of the defining polynomial of the Riemann Surface X. }
	return X`HomoDefPol;
end intrinsic;
intrinsic FunctionField(X::RieSrf) -> FldFun
{ Returns the function field of the defining polynomial of the Riemann Surface X. }
	return X`FunctionField;
end intrinsic;
intrinsic BasePoint(X::RieSrf) -> RieSrfPt
{ Returns the base point of the Riemann Surface X. }
	return X`BasePoint;
end intrinsic;
intrinsic Degree(X::RieSrf) -> RngIntElt
{ Returns the degree of X as cover of the projective line. }
	return X`Degree[1];
end intrinsic;
intrinsic BranchPoints(X::RieSrf) -> Tup
{ Returns the branch points of the Riemann Surface X. }
	return ChangeUniverse(X`BranchPoints,X`ComplexFields[3]);
end intrinsic;
intrinsic DiscriminantPoints(X::RieSrf) -> SeqEnum[FldComElt]
{ Returns the discriminant points of the Riemann Surface X. }
	return ChangeUniverse(X`DiscriminantPoints,X`ComplexFields[3]);
end intrinsic;
intrinsic IsSuperelliptic(X::RieSrf) -> BoolElt
{ Returns true if the Riemann surface X is superelliptic and false otherwise. }
	return X`IsSuperelliptic;
end intrinsic;
intrinsic HolomorphicDifferentials(X::RieSrf) -> Tup
{ Returns a description of the basis of holomorphic differentials that is being used. }
	if X`IsSuperelliptic then
		DFF := X`HolomorphicDifferentials;
		Res := <>;
		for k in [1..DFF[2]] do
			for j in [1..DFF[3][k]] do
				Append(~Res,[j-1,DFF[1]+k-1]);
			end for;
		end for;
		return Res;
	else
		return <X`HolomorphicDifferentials[1],X`HolomorphicDifferentials[2]>;
	end if;
end intrinsic;
intrinsic MonodromyRepresentation(X::RieSrf) -> SeqEnum[GrpPermElt]
{ Returns the monodromy description of the Riemann surface. }
	return X`LocalMonodromy;
end intrinsic;
intrinsic BaseRing(X::RieSrf) -> RieSrfPt
{ Returns the base ring of the defining polynomial of the Riemann Surface X. }
	return BaseRing(Parent(X`DefiningPolynomial));
end intrinsic;
intrinsic SingularPoints(X::RieSrf) -> SeqEnum[SeqEnum]
{ Returns the coordinates of the singular points of the projective closure of the affine curve defining X. }
	if not assigned X`SingularPoints then
		AnalyzeSpecialPoints(X);
	end if;
	return X`SingularPoints;
end intrinsic;
intrinsic FundamentalGroup(X::RieSrf : Extended := true ) -> SeqEnum[CChain]
{ Returns the closed chains that generate the fundamental group of the complex plane punctured by the discriminant points of X. }
	require not X`IsSuperelliptic : "Fundamental group is not computed for superelliptic Riemann surfaces.";
	if Extended then
		return X`ClosedChains cat [X`InfiniteChain];
	else
		return X`ClosedChains;
	end if;
end intrinsic;
intrinsic RamificationPoints(X::RieSrf) -> SeqEnum[RieSrfPt]
{ Returns the defining polynomial of the Riemann Surface X. }
	if not assigned X`RamificationPoints then
		if X`IsSuperelliptic then
			AllPoints := X`CriticalPoints cat X`InfinitePoints;
		else
			Chains := FundamentalGroup(X:Extended);
			AllPoints := &cat[ Ch`Points : Ch in Chains ];
		end if;
		X`RamificationPoints := [ Pt : Pt in AllPoints | RamificationIndex(Pt) gt 1 ];
	end if;
	return X`RamificationPoints;
end intrinsic;

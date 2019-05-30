/*******************************************************************************

	Abel-Jacobi map of points at infinity for Riemann surfaces
 
	Christian Neurohr, May 2019

*******************************************************************************/

import "miscellaneous.m": EmbedPolynomial, ModifiedFiber, SE_DKPEB;
import "fundamentalgroup.m": SE_Edge, EdgeData, Mixed_Params_AJM;
import "paths.m": CInfiniteLine, PermuteMatrix;
import "integration.m": DE_Params_Path, SE_Integrals_Edge_AJM, SE_DE_Integration, SE_GJ_Integration;

procedure SE_AJM_InftyPoints( X, k )
/* Abel-Jacobi map of D = [ P_infty^k - P_0 ], where P_infty^k = (\zeta_\delta^k,0) in the (r,t)-model of the curve */
	g := X`Genus;
	m := X`Degree[1];
	n := X`Degree[2];
	delta,a,b := Xgcd(m,n);
	assert X`IsSuperelliptic;
	assert k in [1..delta];
	R := RealField(Precision(X`ComplexFields[2]));
	if not IsDefined(X`AJM_InfinitePoints,k) then 
		if delta eq 1 then
			Append(~X`AJM_InfinitePoints,X`AJM_SumOfInftyPoints);
		elif &and[IsDefined(X`AJM_InfinitePoints,j) : j in Remove([1..delta],k) ] then
			X`AJM_InfinitePoints[k] := X`AJM_SumOfInftyPoints - &+[ X`AJM_InfinitePoints[j] : j in Remove([1..delta],k) ];
		else
		while a ge 0 do
			a -:= n;
			b +:= m;
		end while;
		assert a*m + b*n eq delta;
		M := Round(m/delta);
		N := Round(n/delta);
		/* Need more precision? */
		if not IsDefined(X`ComplexFields,4) then
			C<I> := ComplexField((Ceiling((m/10))+1)*X`Prec+2*n);	
			vprint RS,1 : "New complex field",C;
			X`ComplexFields[4] := C;
			X`DiscriminantPoints := SE_DKPEB(X`DefiningPolynomial,X`DiscriminantPoints,Precision(C));
			X`ComplexDefPol := ChangeRing(X`DefiningPolynomial,C);
		else
			C<I> := X`ComplexFields[4];
		end if;
		Ct<t> := PolynomialRing(C); 		
		/* m-th root of leading coefficient */
		LC_mi := Exp( (1/m) * Log(LeadingCoefficient(X`ComplexDefPol)));
		if M eq 1 then
			// Solve polynomial g(1,t) = 0 
			p := &*[ (1 - x*(t^M)) : x in X`DiscriminantPoints ] - 1;
			assert Degree(p) in [n,n-1];
			pC := Coefficients(p);
			Inf_Ord := Min([ j : j in [1..Degree(p)+1] | Abs(pC[j]) gt X`Error ]) - 1;
			if Inf_Ord eq 1 then
				/* Obtain the other integrals by multiplication with correct powers of zeta */
				jPows := X`HolomorphicDifferentials[4];
				ZetaPows := [];
				for k in [1..g] do
					Pow := Round(-2*m*(a+b*N)*jPows[k]/delta) mod (2*m) + 1;
					Append(~ZetaPows,Pow);
				end for; 
				/* Define g(1,t)/t^ord */
				pt := &+[ pC[j+1] * t^(j-Inf_Ord) : j in [Inf_Ord..Degree(p)] | Abs(pC[j+1]) gt X`Error ];
				dpt := Degree(pt);
				/* Compute roots */
				Rts_pt := RootsNonExact(pt);
				/* Get points and multiplicities */
				Points := < >; 
				Coeffs := [];
				for j in [1..dpt] do
					t_j := Rts_pt[j];
					ltj := Log(t_j);
					x_j := Exp(-M*ltj);
					y_j := Exp(-N*ltj)*LC_mi;
					Append(~Points,[x_j,y_j]);
				end for;
				vprint RS,1 : "Good case: have to compute",#Points,"integrals!";
				TotalComplexIntegral := Matrix(X`ComplexFields[2],g,1,[]);
				/* Is zero a branch point? */
				if Degree(p) eq (n-1)*M then
					Dist, Ind := Distance(Zero(C),X`BranchPoints);
					assert Dist lt X`Error;
					TotalComplexIntegral -:= (N*m-M) * X`AJM_RamificationPoints[Ind];
				end if;
				/* Sort out ramification points */
				ComplexEdges := [];
				for P in Points	do
					Dist, Ind := Distance(P[1],X`DiscriminantPoints);
					TotalComplexIntegral +:= X`AJM_RamificationPoints[Ind];
					if Dist gt X`Error then
						NewEdge := SE_Edge(Ind,P);
						EdgeData(NewEdge,X`DiscriminantPoints,[],X`Degree[1],X`Degree[2]);
						Append(~ComplexEdges,NewEdge);
					end if;
				end for;
				/* Integration parameters */
				GJ_Params, DE_Params, GJ_Edges, DE_Edges := Mixed_Params_AJM(ComplexEdges,X);
				/* Maximal absolute value */
				MaxAbs := Max( [ P[1] : P in GJ_Params ] cat [ P[1] : P in DE_Params ]);

				/* Even more precision? */
				ExtraPrec := 2*Max(5,Ceiling(Log(10,Binomial(X`Degree[2],Floor(X`Degree[2]/4))*MaxAbs)));
				if ExtraPrec+X`Prec gt Precision(X`ComplexFields[3]) then
					vprint RS,2 :"Extra precision (AJM):",ExtraPrec;
					C<I> := ComplexField(Precision(X`ComplexFields[3])+ExtraPrec);
					X`ComplexFields[3] := C;
					if Precision(C) gt Precision(X`ComplexFields[4]) then
						X`DiscriminantPoints := SE_DKPEB(X`DefiningPolynomial,X`DiscriminantPoints,Precision(C));
						X`ComplexDefPol := ChangeRing(X`DefiningPolynomial,C);
						X`ComplexFields[4] := C;
					end if;
				end if;

				/* Compute integration schemes */
				SE_DE_Integration(DE_Params,X:AJM);
				SE_GJ_Integration(GJ_Params,X:AJM);

				/* Actual integrations from P_k to P */
				ComplexIntegrals := [ Matrix(X`ComplexFields[3],g,1,[]) : j in [1..delta] ];
				for CE in DE_Edges cat GJ_Edges do
					ComplexIntegral0 := SE_Integrals_Edge_AJM(CE,X);
					ComplexIntegrals[1] +:= Matrix(X`ComplexFields[3],g,1,ComplexIntegral0);
					for k in [2..delta] do
						CI0seq := Eltseq(ComplexIntegral0);
						ComplexIntegral0 := Matrix(X`ComplexFields[3],g,1,[ X`Zetas[ZetaPows[j]] * CI0seq[j] : j in [1..g]]);
						ComplexIntegrals[k] +:= ComplexIntegral0;
					end for;
				end for;
				TotalComplexIntegrals := [ TotalComplexIntegral + ChangeRing(ComplexIntegrals[j],X`ComplexFields[2]) : j in [1..delta] ];
				/* Save results in correct order (according to the paper) */
				X`AJM_InfinitePoints := [ TotalComplexIntegrals[k] : k in [2..delta] ];
				Append(~X`AJM_InfinitePoints,TotalComplexIntegrals[1]);
			end if;
		end if;
		if M gt 1 or Inf_Ord ne 1 then
			r := Exp(2*Pi(C)*I*k/delta);
			pt := &*[ (1 - x*(r+t)^b*(t^M)) : x in X`DiscriminantPoints ] - (r+t)^delta;
			pC := Coefficients(pt);
			pt := &+[ pC[j] * t^(j-1) : j in [1..Degree(pt)+1] | Abs(pC[j]) gt X`Error ];
			dpt := Degree(pt);
			assert dpt in [n*(M+b),(n-1)*(M+b)];
			assert Abs(pC[2]) gt X`Error;
			/* Compute roots */
			Rts_pt := RootsNonExact(pt);
			/* Get points and multiplicites */
			Points := []; Mults := [];
			for j in [1..dpt] do
				t_j := Rts_pt[j];
				if Abs(t_j) gt X`Error then
					lrtj := Log(r+t_j);
					ltj := Log(t_j);
					x_j := Exp(-((b*lrtj+M*ltj)));
					y_j := Exp(a*lrtj-N*ltj)*LC_mi;
					Pt := New(RieSrfPt);
					Pt`x := x_j; Pt`y := y_j;
					Pt`RieSrf := X; Pt`IsFinite := true;
					Append(~Points,Pt);
					Append(~Mults,1);
				end if;
			end for;
			assert #Points in [n*b+n*M-1,n*b+n*M-b-M-1];
			vprint RS,1 : "Bad case: have to compute",#Points,"integrals!";
			/* Is Zero a branch point? */
			if dpt eq (n-1)*(M+b) then
				Append(~Points,X![0,0]);
				Append(~Mults,N*m+M+b);
			end if;
			/* Compute AbelJacobi map of divisor divisor */	
			D := Divisor(Points,Mults);
			V := -AbelJacobi(D:Reduction:="None");
			/* Substract the sum of infinite points */
			X`AJM_InfinitePoints[k] := -(D`AJM + b * X`AJM_SumOfInftyPoints);
		end if;
		end if;
	end if;
end procedure;


procedure AJM_DE_InfinitePoints( X )
/* Compute the Abel-Jacobi map from the basepoint to infinity on all sheets using double-exponential integration */
	vprint RS,1 : "Integrating to infinity...";
	NewPrec := true;
	go_on := true;
	CL := ComplexField(5);
	Err := 10^-(Precision(X`ComplexFields[2])+1);
	c := Max([ #cd : cd in  CycleDecomposition(X`InfiniteChain`Permutation) ])+1;
	assert c gt 1;
	m := X`Degree[1];
	RMV := [ Remove([1..m],j) : j in [1..m] ];
	Digits := Precision(X`ComplexFields[2]);
	g := X`Genus;
	h := 16/125;
	Gammas := [];
	OldError := Infinity();
	while go_on do
		go_on := false;
		if NewPrec then
			CC<I> := ComplexField(c*Precision(X`ComplexFields[3]));
			RR := RealField(CC);
			Cz<z> := PolynomialRing(CC);
			Cxy<x,y> := PolynomialRing(CC,2);
			fC := EmbedPolynomial(X`DefiningPolynomial,X`Embedding,Cxy);
			Err2 := Real(((1/2) * 10^-((c-1)*Digits+1))^2); // Error^2
			/* Differentials */
			if X`Baker then
				DFF_Factors := [ Derivative(fC,2) ];
			else
				DFF_Factors := [ EmbedPolynomial(Fac,X`Embedding,Cxy) : Fac in X`HolomorphicDifferentials[1] ];
			end if;
			NewPrec := false;
		end if;
		Gamma := CInfiniteLine(CC!X`BasePoint`x);

		/* Compute double-exponential integration */
		N := Round(7.2/h);
		N2P1 := 2*N+1;
		Abscissas, Weights := TanhSinhIntegrationPoints( N, RR!h );
		Append(~Abscissas,1);

		/* Integrate path to infinity */
		PathDiffMatrix := Matrix(CC,m,g,[]);
		xj, dxj := Gamma`Evaluate(Abscissas[1]);
		yj := ModifiedFiber(fC,Gamma`StartPt);
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
			xj, dxj := Gamma`Evaluate(Abscissas[j+1]);
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
		Gamma`Integrals := ChangeRing(PathDiffMatrix,X`ComplexFields[3]);
		Append(~Gammas,Gamma);

		/* How many correct digits? */
		if go_on eq false then
			vprint RS,2 :  "Testing accuracy...";
			if X`InfiniteChain`Permutation ne Id(Sym(m)) then
				V := Gamma`Integrals - PermuteMatrix(Gamma`Integrals,X`InfiniteChain`Permutation,m,g) -  X`InfiniteChain`Integrals;
				Gamma`Error := Max([ Abs(c) : c in Eltseq(V) ]);
				MABS := Floor(-Log(10,Gamma`Error));
				vprint RS,2 : "Significant digits in AJM_InfinitePoints:",MABS;
				if Gamma`Error gt X`Error then
					if Gamma`Error/OldError gt 1/10 and #Gammas gt 2 then
						print "Warning! Significant digits for integral to infinity:",MABS;
						go_on := false;
						break;
					else
						h := h/2;
						go_on := true;
						OldError := Gamma`Error;
						NewPrec := false;
					end if;
				end if;
			else
				s := #Gammas;
				if s eq 1 then
					go_on := true; h := h/2; NewPrec := false;
				else
					Gamma`Error := Max([ Abs(c) : c in Eltseq(Gammas[s]`Integrals-Gammas[s-1]`Integrals) ]);
					MABS := Floor(-Log(10,Gamma`Error));
					vprint RS,2 : "Significant digits in AJM_InfinitePoints:",MABS;
					if Gamma`Error gt X`Error then
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
	
	Ok, Sigma := Sort(yj,X`Ordering);
	Gamma`Permutation := Inverse(Sigma);
	/* Gamma`Sheets is used to find homogeneous coordinates */
	Gamma`Sheets := [ xj/yj[k] : k in [1..m] ];
	
	/* Save line to infinity */
	X`AJM_InfinitePoints := Gamma;
end procedure;

function StrongApproximation(P0,Index,L)
/* Obtain a rational function that has valuation zero at all places in L, except -1 at L[Index], P0 is a base place and not in L */
	F := FunctionField(P0);
	if #L gt 1 then
		D := 0 * P0 - &+Remove(L,Index);
	else
		D := 0 * P0;
	end if;
	while IsSpecial(D) do
		D +:= P0;
	end while; 
	B := Basis(D);
	a := [ F | ];
	for i in [1..#L] do
		V, f := RiemannRochSpace( D + L[i] );
		W := sub< V | B@@f >;
		U, g := quo< V | W >;
		b := f(U.1@@g);
		Append(~a, b);
	end for;
	return &+ a;
end function;
procedure SpecialPointsByMoving( X : Method := "Swap" )
/* Computes the Abel-Jacobi map of infinite points and singular finite points */
	FF<x,y> := FunctionField(X);
	K := ConstantField(FF);
	C<I> := X`ComplexFields[4];
	Cz<z> := PolynomialRing(C);
	P0 := Floor(X`BasePoint`x);
	P0 := Zeros(x-P0)[1];
	InfXPlaces := Poles(x);
	InfYPlaces := SetToSequence(Set(Poles(y)) diff Set(InfXPlaces));
	X`AJM_SpecialDivisors := [];
	IP := X`InfinitePoints;

	/* Try numerical integration first */
	if not assigned X`AJM_InfinitePoints then 
		AJM_DE_InfinitePoints(X);
	end if;
	if X`AJM_InfinitePoints`Error lt X`Error then
		if #InfXPlaces eq 1 then
			PlAtInf := InfXPlaces[1];
			assert Degree(PlAtInf) eq #IP;
			if #IP eq 1 then
				D := 1 * IP[1];
			else
				D := &+IP;
			end if;
			D`AJM := AbelJacobi(D:Reduction:="None");
			D`Place := PlAtInf;
			Remove(~InfXPlaces,1);
			Append(~X`AJM_SpecialDivisors,D);
		end if;
	else
		print "Points at infinity: Double-exponential integration failed. Using strong approximation!";
	end if;
	Indx := [];
	for k in [1..#InfYPlaces] do
		PlAtInfY := InfYPlaces[k];
		PX := Evaluate(x,PlAtInfY);
		NrPl := #[ Pl : Pl in InfYPlaces | Evaluate(x,Pl) eq PX ];
		if NrPl eq 1 then
			PXFR := Set(ChangeUniverse(Conjugates( AbsoluteField(Parent(PX))!PX : Precision:=Precision(C)),C));
			Pts := [];
			for xk in PXFR do
				Dist, Ind := Distance(xk,X`DiscriminantPoints);
				if Dist lt X`Error then
					Pts cat:= [ Pt : Pt in X`ClosedChains[Ind]`Points | not Pt`IsFinite ];
				end if;
			end for;
			assert #Pts eq Degree(PlAtInfY);
			if #Pts eq 1 then
				D := 1 * Pts[1];
			else
				D := &+Pts;
			end if;
			D`AJM := AbelJacobi(D:Reduction:="None");
			D`Place := PlAtInfY;
			Append(~Indx,k);
			Append(~X`AJM_SpecialDivisors,D);
		end if;
	end for;
	Reverse(~Indx);
	for Ind in Indx do
		Remove(~InfYPlaces,Ind);
	end for;
	InfPlaces := Set(InfXPlaces cat InfYPlaces);

	/* Finite singularities? */
	for P in X`FiniteSingularities do
		/* TODO: should get MiPo directly from factorization of discriminant; this might fail over number fields */
		MiPo := MinimalPolynomial(P[1],100);
		InfPlaces join:= Set(Zeros(Evaluate(MiPo,x)));
	end for;
	InfPlaces := SetToSequence(InfPlaces);

	while #InfPlaces gt 0 do
		Pl := InfPlaces[1];
		/* Compute meromorphic function via strong approximation */
		ff := StrongApproximation(P0,1,InfPlaces);

		/* Construct support of new divisor */
		NewPoints := []; NewMults := [];
		ff_div := Divisor(ff);
		S,M := Support(ff_div);
		Pos := Position(S,Pl);
		assert Pos ne 0;
		assert M[Pos] eq -1;
		assert &+[ M[t]*Degree(S[t]) : t in [1..#S]] eq 0;
		Remove(~S,Pos);
		Remove(~M,Pos);

		/* Now build DivRieSrfElt! */
		ExtraDiv := [];
		for l in [1..#S] do
			P := S[l];
			if P eq P0 then
				FIBX0 := X`Fiber(X`BasePoint`x);
				for n in [1..X`Degree[1]] do
					Append(~NewPoints,X![X`BasePoint`x,FIBX0[n]]);
					Append(~NewMults,M[l]);
				end for;
			else
				pos := Position([Div`Place : Div in X`AJM_SpecialDivisors],P);
				if pos ne 0 then
					Append(~ExtraDiv,<pos,M[l]>);
				else
					PX := Evaluate(x,P);
					PY := Evaluate(y,P);
					if PX eq 0 and PY eq 0 then
						PXFR := [ Zero(C) ]; PYFR := [ Zero(C) ];
					else
						if PX eq 0 then
							PXFR := [ Zero(C) : j in [1..Degree(P)*Degree(K)] ];
						else
							PXFR := ChangeUniverse(Conjugates( AbsoluteField(Parent(PX))!PX : Precision:=Precision(C)),C);
						end if;
						if PY eq 0 then
							PYFR := [ Zero(C) : j in [1..Degree(P)*Degree(K)] ];
						else
							PYFR := ChangeUniverse(Conjugates( AbsoluteField(Parent(PY))!PY : Precision:=Precision(C)),C);
						end if;
					end if;
					assert #PYFR eq #PXFR;
					for m in [1..#PXFR] do
						yn, Pt := IsCoercible(X,[PXFR[m],PYFR[m]]);
						if yn then
							Append(~NewPoints,Pt);
							Append(~NewMults,M[l]);
						end if;
					end for;
				end if;
			end if;
		end for;
		D := Divisor(NewPoints,NewMults);
		/* Compute Abel-Jacobi map */
		D`AJM := AbelJacobi(D:Reduction:="None",Method:=Method);
		for DD in ExtraDiv do
			D +:= DD[2] * X`AJM_SpecialDivisors[DD[1]];
		end for;
		D`FFDiv := ff_div;
		D`Place := Pl;
		Append(~X`AJM_SpecialDivisors,D);
		Remove(~InfPlaces,1);
	end while;
end procedure;

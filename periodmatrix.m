/*******************************************************************************

	Period matrices of Riemann surfaces
 
	Christian Neurohr, September 2018

*******************************************************************************/

import "paths.m": ReversePath;
import "miscellaneous.m": IntGroups, EmbedPolynomial;
import "integration.m": GL_Integration, CC_Integration, GLCC_Params_Path, DE_Integration, DE_Params_Path, HeuristicBound, SE_Integrals_Tree, SE_DE_Integration, SE_GJ_Integration;
import "homology.m": SE_IntersectionMatrix, SE_IntersectionNumber, SymplecticTransformation;

intrinsic BigPeriodMatrix( X::RieSrf ) -> Mtrx
{ Returns the big period matrix associated to the Riemann surface X. }
	C<I> := X`ComplexFields[1];
	return ChangeRing(X`BigPeriodMatrix,C);
end intrinsic;
intrinsic SmallPeriodMatrix( X::RieSrf : Check := true ) -> Mtrx
{ Returns the small period matrix associated to the Riemann surface X. }
	if not assigned X`SmallPeriodMatrix then
		g := X`Genus;
		APMINV := ColumnSubmatrixRange(X`BigPeriodMatrix,1,g)^(-1);
		Tau := APMINV * ColumnSubmatrixRange(X`BigPeriodMatrix,g+1,2*g);
		if Check then
			/* Testing for symmetry of the period matrix */
			vprint RS,1 : "Testing symmetry...";
			MaxSymDiff := 0;
			for j in [1..g] do
				for k in [j+1..g] do
					MaxSymDiff := Max(MaxSymDiff,Abs(Tau[j][k]-Tau[k][j]));
				end for;
			end for;
			vprint RS,2 : "Maximal symmetry deviation:",ChangePrecision(Real(MaxSymDiff),10);
			if MaxSymDiff ge X`Error then
				print "Small period matrix: Requested accuracy could not not be reached.";
				print "Significant digits:",Floor(-Log(10,MaxSymDiff));
			end if;	
			/* Testing positive definiteness of the imaginary part of the period matrix */
			vprint RS,1 : "Testing positive definiteness...";
			Tau_Im := Matrix(RealField(X`Prec),g,g,[]);
			for j in [1..g] do
				Tau_Im[j][j] := Im(Tau[j][j]);
				for k in [j+1..g] do
					Tau_Im[j][k] := Im(Tau[j][k]);
					Tau_Im[k][j] := Tau_Im[j][k];
				end for;
			end for;
			assert IsPositiveDefinite(Tau_Im);
		end if;
		X`SmallPeriodMatrix := Tau;
		X`ReductionMatricesComplex := < ChangeRing(APMINV,X`ComplexFields[2]) >;
	end if;
	C<I> := X`ComplexFields[1];
	return ChangeRing(X`SmallPeriodMatrix,C);
end intrinsic;
procedure ReductionMatrix(X,Type)
/* Compute reduction matrix for the Abel-Jacobi map */
	g := X`Genus;
	if Type eq "Real" and not assigned X`ReductionMatrixReal then
		/* Embed big period matrix in \R^{2g \times 2g} */
		BPM := X`BigPeriodMatrix;
		M := Matrix(Parent(Re(BPM[1][1])),2*g,2*g,[]);
		for j in [1..g] do
			for k in [1..g] do
				M[j,k] := Re(BPM[j,k]);
				M[j+g,k] := Im(BPM[j,k]);
				M[j,k+g] := Re(BPM[j,k+g]);	
				M[j+g,k+g] := Im(BPM[j,k+g]);
			end for;
		end for;
		/* Matrix inversion */
		X`ReductionMatrixReal := ChangeRing(M^(-1),RealField(Precision(X`ComplexFields[2])));
	else
		if not assigned X`SmallPeriodMatrix then
			Tau := SmallPeriodMatrix(X);
		end if;
		if #X`ReductionMatricesComplex eq 1 then
			ITau := Matrix(g,g,[Im(a) : a in Eltseq(X`SmallPeriodMatrix)]);
			Append(~X`ReductionMatricesComplex,ChangeRing(ITau^(-1),RealField(Precision(X`ComplexFields[2]))));
		end if;
	end if;
end procedure;


procedure PeriodMatrix(X)
/* Computes a big period matrix associated to the Riemann surface X */

	/* Holomorphic differentials and genus */
	g := X`Genus;
	DFF := X`HolomorphicDifferentials; 

	/* Symmetric group on m elements (sheets) */
	//m := X`Degree[1];
	m := Degree(X`AffineModel,2);
	Sym := Sym(m);
	Id := Id(Sym);
	vprint RS,1 : "#Sheets:",m;
	NumberOfCycles := 2*g + m -1;

	/* Complex field used for computations */
	C<I> := X`ComplexFields[2];
	CompPrec := Precision(C);
	vprint RS,1 : "Adjusted precision:",Precision(C);

	/* Complex field of maximal precision */
	CC<I> := X`ComplexFields[3];
	RR := RealField(Precision(CC));
	CC_0 := Zero(CC); CC_1 := One(CC);  OH := CC!(1/2);
	MaxPrec := Precision(CC);
	Cz<z> := PolynomialRing(CC); Czw<w> := PolynomialRing(Cz);
	Cxy<x,y> := PolynomialRing(CC,2);
	OneMatrix := Matrix(CC,m,g,[ CC_1 : j in [1..m*g]] );
	vprint RS,1 : "Precision:",X`Prec;
	vprint RS,1 : "Computational precision:",CompPrec;
	vprint RS,1 : "Maximal precision (Period matrix):",MaxPrec;
	f := ChangeRing(X`ComplexDefPol,CC);
	print "f:",f;
	/* Differentials */
	if X`Baker then
		DFF_Factors := [ ChangeRing(Derivative(f,2),CC) ];
		DFF_Test := [ ChangeRing(Derivative(f,2),ComplexField(10)) ];
	else
		DFF_Factors := [ EmbedPolynomial(Fac,X`Embedding,Cxy) : Fac in DFF[1] ];
		DFF_Test := X`HolomorphicDifferentials[5];
	end if;
	
	/* Number of paths */
	NPath := #X`PathPieces;
	vprint RS,1 : "Number of paths:",NPath;

	/* Compute integration schemes */
	RL := RealField(3);
	Err := RL!(10^-(Precision(X`ComplexFields[2])+1));
	vprint RS,1 : "Error:",Err;
	if X`IntMethod eq "DE" then
		for Gamma in X`PathPieces do
			DE_Params_Path(X`DiscriminantPoints,Gamma);
		end for;
		IntParPaths := [ Gamma`IntPar : Gamma in X`PathPieces ];
		Sort(~IntParPaths);
		rmi := IntParPaths[1];
		rma := IntParPaths[NPath];
		NSchemes := Max(Ceiling(20*(rma-rmi)),1);
		Groups := [ [] : j in [1..NSchemes] ];
		for r in IntParPaths do
			t := Max(Ceiling(20*(r-rmi)),1);
			Append(~Groups[t],r);
		end for;
		vprint RS,2 : "Groups:",Groups;
		Lr := [ (29/30) * rmi ] cat [ (29/30) * Min(g) : g in Remove(Groups,1) | #g gt 0 ];
		vprint RS,2 : "Lr:",Lr;
		vprint RS,2 :"MinDE_r:",rmi;
		vprint RS,2 :"MaxDE_r:",rma;
		/* Compute heuristic bounds */
		Bound2 := [];
		for Gamma in X`PathPieces do
			for SGamma in Gamma`Subpaths do
				HeuristicBound(SGamma,DFF_Test,Lr,X);
				Bound2 cat:= SGamma`Bounds;
			end for;
		end for;
		Bound2 := Max(Bound2);
		vprint RS,1 : "Bound2:",Bound2;
		Append(~X`Bounds,Bound2);
		Bound := Max(X`Bounds);
		Bound := Bound2;
		vprint RS,1 : "Bound:",Bound;
		X`IntSchemes["DE"] cat:= [ DE_Integration(RR!r,CompPrec:Bounds:=[Bound,Bound]) : r in Lr ];
	elif X`IntMethod in ["GL","CC"] then
		for Gamma in X`PathPieces do
			GLCC_Params_Path(X`LPDP,Gamma,Err,X`IntMethod);
		end for;
		IntParPaths := [];
		for Gamma in X`PathPieces do
			if Gamma`Type eq "LineSegment" then
				IntParPaths cat:= [ SubGamma`IntPar : SubGamma in Gamma`Subpaths ];
			else
				IntParPaths cat:= [ Gamma`IntPar ];
			end if;
		end for;
		Sort(~IntParPaths);
		rm := IntParPaths[1];
		eps := 1/100;
		if X`IntMethod eq "GL" then
			IntGrps := IntGroups(IntParPaths,rm,"GL");	
		else
			IntGrps := IntGroups(IntParPaths,rm,"CC");
		end if;
		vprint RS,2 : "IntGroups:",IntGrps;
		if rm le 1+(1/50) then
				Lr := [(1/2)*(rm+1)];
			else
				Lr := [rm-eps];
		end if;
		Lr cat:= [ Min(g) - eps : g in Remove(IntGrps,1) | #g gt 2 ];		
		vprint RS,2 : "Lr:",Lr;
		/* Compute heuristic bounds */
		Bound2 := [];
		for Gamma in X`PathPieces do
			for SGamma in Gamma`Subpaths do
				HeuristicBound(SGamma,DFF_Test,Lr,X);
				Bound2 cat:= SGamma`Bounds;
			end for;
		end for;
		Bound2 := Max(Bound2);
		vprint RS,1 : "Heuristic bound:",Bound2;
		Append(~X`Bounds,Bound2);
		Bound := Max(X`Bounds);
		Bound := Bound2;
		vprint RS,1 : "Bound:",Bound;
		if X`IntMethod eq "GL" then
			X`IntSchemes["GL"] cat:= [ GL_Integration(r,MaxPrec,Err:Bound:=Bound) : r in Lr ];
		else
			X`IntSchemes["CC"] cat:= [ CC_Integration(r,MaxPrec,Err:Bound:=Bound) : r in Lr ];
		end if;
	elif X`IntMethod eq "Mixed" then
		vprint RS,1 : "Mixed integration:",X`IntMethod;
		/* When to use DE integration? */
		k := (103/100);
		for Gamma in X`PathPieces do
			GLCC_Params_Path(X`LPDP,Gamma,Err,"GL");
		end for;
		DE_PathPieces := []; DE_IntPars := [];
		GL_PathPieces := []; GL_IntPars := [];
		for Gamma in X`PathPieces do
			for SGamma in Gamma`Subpaths do
				if SGamma`IntPar lt k then
					vprint RS,2 : "SGamma:",SGamma;
					vprint RS,2 : "SGamma`r(GL/CC):",SGamma`IntPar;
					delete SGamma`IntPar;
					DE_Params_Path(X`LPDP,SGamma);
					assert SGamma`IntPar lt k;
					vprint RS,2 : "SGamma`r(DE):",SGamma`IntPar;
					vprint RS,2 : "Index:",Position(X`PathPieces,Gamma);
					Append(~DE_PathPieces,SGamma);
					Append(~DE_IntPars,SGamma`IntPar);
				else
					Append(~GL_PathPieces,SGamma);
					Append(~GL_IntPars,SGamma`IntPar);
				end if;
			end for;
		end for;
		vprint RS,2 : "DE_IntPars:",DE_IntPars;
		vprint RS,2 : "DE_PathPieces:",DE_PathPieces;
		GL_Lr := [];
		if #GL_IntPars gt 0 then
			Sort(~GL_IntPars);
			rm := GL_IntPars[1];
			IntGrps := IntGroups(GL_IntPars,rm,"GL");	
			vprint RS,2 : "Groups:",IntGrps;
			eps := 1/100;
			if rm le 1+(1/50) then
					Append(~GL_Lr,(1/2)*(rm+1));
				else
					Append(~GL_Lr,rm-eps);
			end if;
			GL_Lr cat:= [ Min(g) - eps : g in Remove(IntGrps,1) | #g gt 2 ];		
			vprint RS,2 : "GL_Lr:",GL_Lr;
			/* Compute heuristic bounds */
			Bound2 := [];
			for Gamma in X`PathPieces do
				for SGamma in Gamma`Subpaths do
					HeuristicBound(SGamma,DFF_Test,GL_Lr,X);
					Bound2 cat:= SGamma`Bounds;
				end for;
			end for;
			Bound2 := Max(Bound2);
			vprint RS,1 : "Heuristic bound:",Bound2;
			Append(~X`Bounds,Bound2);
			Bound := Max(X`Bounds);
			Bound := Bound2;
			vprint RS,1 : "Bound:",Bound;
			X`IntSchemes["GL"] cat:= [ GL_Integration(r,MaxPrec,Err:Bound:=Bound) : r in GL_Lr ];
		end if;				
		DE_Lr := [];
		NDEP := #DE_IntPars;
		if NDEP ne 0 then
			Sort(~DE_IntPars);
			rmi := DE_IntPars[1];
			rma := DE_IntPars[NDEP];
			NSchemes := Max(Min(Floor(NDEP/2),Floor(20*(rma-rmi))),1);
			vprint RS,2 : "NSchemes(DE):",NSchemes;
			if NSchemes eq 1 and Abs(rmi-rma) lt (1/20) then
				Append(~DE_Lr,(19/20) * rmi);
			else
				DE_Lr cat:= [ (19/20) * ((1-t/NSchemes)*rmi + t/NSchemes*rma) : t in [0..NSchemes] ];
			end if;
			vprint RS,2 : "DE_Lr:",DE_Lr;
			/* Compute heuristic bound */
			Bound2 := [];
			for Gamma in DE_PathPieces do
				for SGamma in Gamma`Subpaths do
					HeuristicBound(SGamma,DFF_Test,DE_Lr,X);
					Bound2 cat:= SGamma`Bounds;
				end for;
			end for;
			Bound2 := Max(Bound2);
			Append(~X`Bounds,Bound2);
			Bound := Max(X`Bounds);
			Bound := Bound2;
			vprint RS,1 : "Bound:",Bound;
			X`IntSchemes["DE"] cat:= [ DE_Integration(RR!r,CompPrec:Bounds:=[Bound,Bound]) : r in DE_Lr ];
		end if;
	else
		error Error("Invalid integration method.");
	end if;
	vprint RS,2 : "Integration schemes(GL):",X`IntSchemes["GL"];
	vprint RS,2 : "Integration schemes(CC):",X`IntSchemes["CC"];
	vprint RS,2 : "Integration schemes(DE):",X`IntSchemes["DE"];

	// Count total number of integration points
	TOTALPOINTS := 0;

	/* Analytic continuation */
	RMV := [ Remove([1..m],j) : j in [1..m] ];
	Err2 := Err^2/4; // Error^2
	function DistSquared(Z)
		DistsSquared := [];
		for k in [1..m] do
			for kk in [k+1..m] do
				zz := Z[k]-Z[kk];
				Append(~DistsSquared,Re(zz)^2+Im(zz)^2);
			end for;
		end for;
		return Min(DistsSquared);
	end function;
	CL := ComplexField(16); 
	function ACRecursion(p,x1,x2,Z)
		px2 := Evaluate(p,[x2,z]);
		px2 *:= 1/LeadingCoefficient(px2);
		W := [ Evaluate(px2,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
		w0 := Max( [ (RL!Re(W[j]))^2+(RL!Im(W[j]))^2 : j in [1..m] ]);
		if w0 lt Err2 then
			return Z;
		end if;
		ChangeUniverse(~Z,CL);
		if 16*w0 lt DistSquared(Z) then
			repeat
				Z := [ Z[j] - W[j] : j in [1..m] ];
				ChangeUniverse(~Z,ComplexField(Min(MaxPrec,2*Precision(Universe(Z)))));
				W := [ Evaluate(px2,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
				w0 := Max([ (RL!Re(W[j]))^2+(RL!Im(W[j]))^2 : j in [1..m] ]);
			until w0 lt Err2;
			return Z;
		else
			x1x2 := (x1+x2)*OH;
			return ACRecursion(p,x1x2,x2,ACRecursion(p,x1,x1x2,Z));
		end if;	
	end function;

	for l in [1..NPath] do
		Gamma := X`PathPieces[l];
		vprint RS,2 : "#####################################################################";
		vprint RS,2 : "Integrating path (#",l,"):",Gamma,"of length",ChangePrecision(Gamma`Length,10),"and IntPar:",Gamma`IntPar;
		
		/* Total integral along Gamma */
		Gamma`Integrals := Matrix(CC,m,g,[]);

		/* Start with fiber above start point */
		yj := X`Fiber(Gamma`Subpaths[1]`StartPt);

		for t in [1..#Gamma`Subpaths] do
			SGamma := Gamma`Subpaths[t];
			if #Gamma`Subpaths gt 1 then
				vprint RS,2 : "Integration subpath:",SGamma,"of length",ChangePrecision(SGamma`Length,10),"with IntPar:",SGamma`IntPar;
			end if;
			
			/* Use correct integration scheme */
			IntSch := X`IntSchemes[SGamma`IntMethod][SGamma`IN];
			/* Append 1 */
			Abscissas := Append(IntSch`Abscissas,1);
		
			/* Integrals along subpath SGamma */
			PathDiffMatrix := Matrix(CC,m,g,[]);
			TOTALPOINTS +:= IntSch`N; 
			vprint RS,2 : "Number of Points:",IntSch`N;
			xj, dxj := SGamma`Evaluate(Abscissas[1]);
			yj := ACRecursion(f,SGamma`StartPt,xj,yj);
			
			if SGamma`Type eq "LineSegment" then
				for j in [1..IntSch`N] do
					OneMat := X`DFFEvaluate(DFF_Factors,xj,yj,m);
					OneMat *:= (IntSch`Weights[j]);
					PathDiffMatrix +:= OneMat;
					nxj := SGamma`Evaluate(Abscissas[j+1]);
					yj := ACRecursion(f,xj,nxj,yj);
					xj := nxj;
				end for;
				Gamma`Integrals +:= PathDiffMatrix * dxj;
			else
				for j in [1..IntSch`N] do
					OneMat := X`DFFEvaluate(DFF_Factors,xj,yj,m);
					OneMat *:= (IntSch`Weights[j] * dxj);
					PathDiffMatrix +:= OneMat;
					nxj, ndxj := SGamma`Evaluate(Abscissas[j+1]);
					yj := ACRecursion(f,xj,nxj,yj);
					xj := nxj; dxj := ndxj;
				end for;
				Gamma`Integrals +:= PathDiffMatrix;
			end if;
		end for;
		/* Testing accuracy of integration */
		for k in [1..g] do
			Val := Abs(&+[ z : z in Eltseq(ColumnSubmatrix(PathDiffMatrix,k,1))]);
			if Val gt X`Error then
				print "Warning: sum of path diff values:",Val;
				error Error("Error while integrating.");
			end if;
		end for;
		/* Assign permutation to Gamma */
		Ok, Sigma := Sort(yj,X`Ordering);
		Gamma`Permutation := Inverse(Sigma);
		vprint RS,2 : "Gamma`Permutation:",Gamma`Permutation;
	end for;
	vprint RS,1 : "Total number of integration points:",TOTALPOINTS;	

	/* Construct closed chains from path pieces */
	X`ClosedChains := [];
	X`BranchPoints := <>;
	OtherChains := [];
	assert #X`IndexPathLists eq #X`DiscriminantPoints;
	for l in [1..#X`IndexPathLists] do
		IndexList := X`IndexPathLists[l];
		NextPath := [];
		for Index in IndexList do
			if Sign(Index) eq 1 then
				Append(~NextPath,X`PathPieces[Index]);
			else
				Append(~NextPath,ReversePath(X`PathPieces[-Index]));
			end if;
		end for;
		NextChain := Chain(NextPath:Center:=X`DiscriminantPoints[l]);
		NextChain`IndexPathList := IndexList;
		NextChain`Radius := X`SafeRadii[l];
		if NextChain`Permutation ne Id then
			Append(~X`ClosedChains,NextChain);
			Append(~X`BranchPoints,NextChain`Center);
		else
			Append(~OtherChains,NextChain);
		end if;
	end for;

	/* Get local monodromy from closed chains */ 
	X`LocalMonodromy := [ Ch`Permutation : Ch in X`ClosedChains ];
	
	/* Get local monodromy at infinity by relation */
	InfPerm := Inverse(&*X`LocalMonodromy);

	/* Chain around infinity */
	InfChain := (&*[ Ch : Ch in X`ClosedChains ])^-1;
	InfChain`Center := Infinity();
	X`InfiniteChain := InfChain;
	if InfPerm ne Id then
		Append(~X`ClosedChains,InfChain);
		Append(~X`LocalMonodromy,InfPerm);
		Append(~X`BranchPoints,Infinity());
	end if;
	vprint RS,2 : "Local monodromy:",X`LocalMonodromy;	

	/* Check Riemann-Hurwitx formula */
	TwoGenusViaMonodromy := 2-2*m;
	for j in [1..#X`LocalMonodromy] do
		CD := CycleDecomposition(X`LocalMonodromy[j]);
		TwoGenusViaMonodromy +:= &+[ #Cyc-1 : Cyc in CD ];
	end for;
	vprint RS,1 : "TwoGenusViaMonodromy:",TwoGenusViaMonodromy;
	assert TwoGenusViaMonodromy eq 2*g;

	/* Monodromy group */
	X`MonodromyGroup := PermutationGroup< m | [Perm : Perm in Set(X`LocalMonodromy)] >;
	
	/* Homology basis */
	Cycles, K, ST := HomologyBasis(X);
	ST_CC := ChangeRing(ST,CC);
	vprint RS,3 : "Intersection matrix:",K;
	vprint RS,3 : "Symplectiv transformation:",ST;	

	StSInts := [ [ CC_0 : j in [1..g] ] ];
	SheetsLeft := Set([j : j in [2..m]]);
	/* Compute period matrix and shange of sheet matrix */
	PM := [];
	for k in [1..NumberOfCycles] do
		Cycle := Cycles[k];
		if #SheetsLeft ne 0 then
			SheetsInCycle := Set([ Cycle[2*l+1] : l in [1..Round((#Cycle-1)/2-1)] ]);
			SheetsMeet := SheetsLeft meet SheetsInCycle;
			SheetsLeft diff:= SheetsMeet;
			SheetsMeet := SetToSequence(SheetsMeet);
		end if;
		CycleDiffVector := Matrix(CC,1,g,[ CC_0 : j in [1..g] ]);
		l := 1;
		while l lt #Cycle do
			Sheet := Cycle[l];
			while Sheet ne Cycle[l+2] do
				CycleDiffVector +:= X`ClosedChains[Cycle[l+1]]`Integrals[Sheet];
				Sheet := Sheet^X`LocalMonodromy[Cycle[l+1]];
				if Sheet in SheetsMeet then
					StSInts[Sheet] := Eltseq(CycleDiffVector);
					Remove(~SheetsMeet,Position(SheetsMeet,Sheet));
				end if;
			end while;
			l +:= 2;
		end while;
		Append(~PM,Eltseq(CycleDiffVector));
	end for;
	/* Sheet to sheet matrix for Abel-Jacobi map */
	X`SheetToSheetIntegrals := Matrix(X`ComplexFields[2],m,g,StSInts);

	/* Periods */
	PM := Matrix(CC,NumberOfCycles,g,PM);

	/* Apply symplectic base change */
	PMAPMB := ST_CC * PM;

	/* Get big period matrix in \C^(g x 2g) */
	X`BigPeriodMatrix := Transpose(RowSubmatrixRange(PMAPMB,1,2*g));

	/* Remove infinite chain and add chains around non-branch points */
	if InfPerm ne Id then
		Prune(~X`ClosedChains);
	end if;
	X`ClosedChains cat:= OtherChains;
	
	/* Order discriminant points according to closed chains */
	X`DiscriminantPoints := [ Ch`Center : Ch in X`ClosedChains ];
	X`SafeRadii := [ Ch`Radius : Ch in X`ClosedChains ];

	/* Confirming the dependence of the cycles 2g+1,...,2g+m-1 */
	DependentColumns := RowSubmatrixRange(PMAPMB,2*g+1,NumberOfCycles);
	vprint RS,2 : "DependentColumns:",DependentColumns;
	assert &and[ Abs(x) lt X`Error : x in Eltseq(DependentColumns) ];
end procedure;



procedure SE_PeriodMatrix( X )
/* Computes a big period matrix associated to the superelliptic Riemann surface X */
	if not assigned X`BigPeriodMatrix then 
	/* Degrees */
	m := X`Degree[1]; n := X`Degree[2];
	
	/* Spanning tree */
	STree := X`SpanningTree;
	vprint RS,1 : "Spanning tree:",STree;	

	/* Holomorphic differentials & genus */
	DFF := X`HolomorphicDifferentials;
	g := X`Genus;
	vprint RS,1 : "Holomorphic differentials:",DFF;
	vprint RS,1 : "Genus:",g;

	/* Integration parameters */
	vprint RS,1 : "Computing integration parameters...";
	vprint RS,1 : "for Gauss-Jacobi integration...";
	SE_GJ_Integration(STree`GJ_Params,X);
	vprint RS,2 : "Integration schemes (GJ):",X`IntSchemes["GJ"];
	vprint RS,1 : "for double-exponential integration...";
	SE_DE_Integration(STree`DE_Params,X);
	vprint RS,2 : "Integration schemes (DE):",X`IntSchemes["DE"];

	/* Computing periods and elementary integrals */
	vprint RS,1 : "Integrating...";
	Periods, ElemInts := SE_Integrals_Tree(X);
	X`ElementaryIntegrals := [];
	for k in [1..n-1] do
		V := Matrix(X`ComplexFields[3],g,1,ElemInts[k]);
		Append(~X`ElementaryIntegrals,V);
	end for;

	/* Make period matrix */
	PM := ZeroMatrix(X`ComplexFields[3],g,(m-1)*(n-1));
	for k in [1..n-1] do
		for l in [1..m-1] do
			Ind := (m-1)*(k-1) + l;
			for j in [1..g] do
				PM[j][Ind] := Periods[k][j][l];
			end for;
		end for;
	end for;

	/* Intersection matrix */
	vprint RS,1 : "Computing spsm-matrix...";
	spsm_Matrix := [ [] : j in [1..n-1] ];
	for j in [1..n-1] do
		spsm_Matrix[j][j] := <1,m-1>;
		for k in [j+1..n-1] do
			spsm := SE_IntersectionNumber(X`SpanningTree`Edges[j],X`SpanningTree`Edges[k],X`DiscriminantPoints,m,n,X`Zetas);
			spsm_Matrix[j][k] := <spsm[1] mod m,spsm[2] mod m>;
		end for;
	end for;
	vprint RS,3: "spsm_Matrix:",spsm_Matrix;

	vprint RS,1 : "Computing intersection matrix...";
	IntMat := SE_IntersectionMatrix(spsm_Matrix,m,n);
	assert Rank(IntMat) eq 2*g;

	/* Symplectic transformation of intersection matrix */
	vprint RS,1 : "Performing symplectic reduction...";
	ST := SymplecticTransformation(IntMat);
	vprint RS,3: "ST:",ST;

	/* Save homology basis */
	X`HomologyBasis := <X`SpanningTree, IntMat, ST>;

	/* Compute big period matrix */
	vprint RS,1 : "Matrix multiplication 1...";
	X`BigPeriodMatrix := PM * ChangeRing(Transpose(RowSubmatrixRange(ST,1,2*g)),X`ComplexFields[3]);

	end if;
end procedure;

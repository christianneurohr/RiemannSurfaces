/*******************************************************************************

	Generators for the first fundamental group of the punctured P^1(C)
 
	Christian Neurohr, September 2018

*******************************************************************************/

import "miscellaneous.m": EmbedPolynomial, CompareByFirstEntry, CompareFldComElt, ModifiedRoots, SortByRealPart, IntGroups_SE;
import "paths.m": CPoint, CLineSegment, CArc, CFullCircle, ReversePath, ModifiedArg;
import "integration.m": Bound_M1, Bound_M2;

RPI := Pi(RealField(30));

/* Do not change these constants */
MaxSafeRadius := 1/4;
SafeRadiusFactor := 2/5;

/* Methods for spanning tree w.r.t minimal euclidean distance */

function FindSet(x,Sets)
	for i in [1..#Sets] do
		if x in Sets[i] then
			return Sets[i],i;
		end if;
	end for;
end function;

function MinimalSpanningTree(Points)
	Edges := []; n := #Points;
	for k in [1..n] do
		for j in [k+1..n] do
			Append(~Edges,<Abs(Points[k]-Points[j]),k,j>);
		end for;
	end for;
	Sort(~Edges,CompareByFirstEntry);
	Sets := [ {k} : k in [1..#Points] ];
	MST_Edges := [];
	j := 1;
	while #MST_Edges lt n-1 do
		S1, s1 := FindSet(Edges[j][2],Sets);
		S2, s2 := FindSet(Edges[j][3],Sets);
		if S1 ne S2 then
			Append(~MST_Edges,<Edges[j][2],Edges[j][3]>);
			Sets[s1] := Sets[s1] join Sets[s2];
			Remove(~Sets,s2);
		end if;
		j +:= 1;
	end while;
	assert #MST_Edges eq n-1;
	return MST_Edges;
end function;

function PathSort(Lines, StartAngle)
/* Sort Lines with common start point by increasing angle where StartAngle is treated as zero */
	d := #Lines;
	if d eq 0 then return []; end if;
	assert #Set([Lines[j]`StartPt : j in [1..d]]) eq 1;
	Center := Lines[1]`StartPt;
	AnglesAndLines := [<ModifiedArg(Lines[j]`EndPt - Center : Rotate:=StartAngle ),Lines[j]> : j in [1..d]];
	Sort(~AnglesAndLines, CompareByFirstEntry);
	return [AnglesAndLines[j][2] : j in [1..d]];
end function;

function FormatedMST(Paths,Points)
/* Choose the basepoint as root of the spanning tree and order edges according to level and angle */
	d := #Paths; k := 1;
	BasePoint := Paths[1]`StartPt;
	Level := [ PathSort( [Paths[j] : j in [1..d] | Paths[j]`StartPt eq BasePoint ],0) ];
	Visited := [BasePoint];
	while #Visited le d do
		NextPoints := [Level[k][j]`EndPt : j in [1..#Level[k]]];
		CurrentLevel := [];
		for j in [1..#NextPoints] do
			CurrentPoint := Level[k][j]`EndPt;
			PreviousPoint := Level[k][j]`StartPt;
			Angle := ModifiedArg(PreviousPoint - CurrentPoint);
			L1 := [ Paths[j] : j in [1..d] | Paths[j]`StartPt eq CurrentPoint and Paths[j]`EndPt notin Visited ];
			L2 := [ ReversePath(Paths[j]) : j in [1..d] | Paths[j]`EndPt eq CurrentPoint and Paths[j]`StartPt notin Visited ];
			L := PathSort(L1 cat L2,Angle); 
			CurrentLevel cat:= L;
		end for;
		if #CurrentLevel gt 0 then
			Append(~Level, CurrentLevel);
		end if;
		k +:= 1;
		Visited cat:= NextPoints;
	end while;
	Paths := &cat[ Path : Path in Level];
	return Paths;
end function;



procedure FindPathsWithDFS( ~OrdDiscPts, ~Path, ~Paths, MST )
/* Conduct a depth-first search (DFS) in the MST (given by levels and line segments sorted by angle) and returns a corresponding ordering of the discriminant points and the paths where the basepoint is the "root" of the tree */
	if #Path ge 1 then
	EndOfPath := true;
	for LS in MST do
		if LS`StartPt eq Path[#Path]`EndPt and LS`EndPt notin OrdDiscPts then
			Append(~OrdDiscPts,LS`EndPt);
			Append(~Path,LS);
			Append(~Paths,Path);
			EndOfPath := false;
			FindPathsWithDFS( ~OrdDiscPts, ~Path, ~Paths, MST );
			break LS;
		end if;
	end for;	
	if EndOfPath then
		Prune(~Path);
		FindPathsWithDFS( ~OrdDiscPts, ~Path, ~Paths, MST );
	end if;
	end if;
end procedure;

function MSTtoMSTX( OldPathPieces, OldIndexPathLists )
/* Creates new PathPieces adding arcs and circles while adjusting the IndexPathLists */
	
	/* Assume first starting point is basepoint */
	BasePoint := OldPathPieces[1]`StartPt;
	C<I> := Parent(BasePoint);

	/* Obtain discriminant points as end points of line segments */
	Points := [ OldPathPiece`EndPt : OldPathPiece in OldPathPieces ];
	d := #Points; opp := #OldPathPieces;

	/* Safe radii */
	SafeRadii := [ Min(MaxSafeRadius,SafeRadiusFactor*Distance(Points[j],Remove(Points,j))) : j in [1..d] ];

	/* Construct new path pieces: first new line segments, then add arcs */
	NewLS := [];
	NewArcs := []; na := 0;
	NewIndexPathLists := [];
	for j in [1..#OldPathPieces] do
		Gamma := OldPathPieces[j];
		NewEndPt := Gamma`Evaluate(-2*SafeRadii[Position(Points,Gamma`EndPt)]/Abs(Gamma`EndPt-Gamma`StartPt)+1);
		if Gamma`StartPt eq BasePoint then
			NewStartPt := BasePoint;
		elif Gamma`StartPt in Points then
			NewStartPt := Gamma`Evaluate(2*SafeRadii[Position(Points,Gamma`StartPt)]/Abs(Gamma`EndPt-Gamma`StartPt)-1);
		else 
			error Error("Not supposed to happen.");
		end if;
		Append(~NewLS,CLineSegment(NewStartPt,NewEndPt));
	end for;

	/*  Construct arcs (and full circles) */
	for k in [d..1 by -1] do
		ll := #OldIndexPathLists[k];
		RevNewIndexPathList := [];
		NewStartPt := NewLS[OldIndexPathLists[k][ll]]`EndPt;
		NewEndPt := NewStartPt;
		Indices := [];
		for l in [1..na] do
			NArc := NewArcs[l];
			if NArc`EndPt eq NewEndPt then
				Append(~Indices,l+opp);
				NewEndPt := NArc`StartPt;
			end if;
		end for;

		NewArc := CArc(NewStartPt,NewEndPt,OldPathPieces[OldIndexPathLists[k][ll]]`EndPt);
		Append(~NewArcs,NewArc); na +:= 1;
		RevNewIndexPathList cat:= Reverse(Append(Indices,opp+na));
		Append(~RevNewIndexPathList, OldIndexPathLists[k][ll]);

		for j in [#OldIndexPathLists[k]-1..1 by -1] do
			NewStartPt := NewLS[OldIndexPathLists[k][j+1]]`StartPt;
			NewEndPt := NewLS[OldIndexPathLists[k][j]]`EndPt;
			Indices := [];
			for l in [1..na] do
				NArc := NewArcs[l];
				if NArc`EndPt eq NewEndPt then
					Append(~Indices,l+opp);
					NewEndPt := NArc`StartPt;
				end if;
			end for;

			/* Complete circle? */
			if NewStartPt ne NewEndPt then
				NewArc := CArc(NewStartPt, NewEndPt, OldPathPieces[OldIndexPathLists[k][j]]`EndPt);
				Append(~NewArcs,NewArc); na +:= 1;
				Append(~Indices,opp+na);
			end if;

			RevNewIndexPathList cat:= [-Ind : Ind in Reverse(Indices)];
			Append(~RevNewIndexPathList, OldIndexPathLists[k][j]);
		end for;

		Ind := 1;
		while RevNewIndexPathList[Ind] gt opp do
			Ind +:= 1;
		end while;
		RevFirst := RevNewIndexPathList[Ind..#RevNewIndexPathList];
		NewIndexPathList := Reverse(RevFirst) cat RevNewIndexPathList[1..Ind-1] cat [-Ind : Ind in RevFirst];
		Append(~NewIndexPathLists, NewIndexPathList);
	end for;
	Reverse(~NewIndexPathLists);

	return NewLS cat NewArcs, NewIndexPathLists;
end function;

intrinsic FundamentalGroup( Points::SeqEnum[FldComElt] : BasePoint := "Clever" ) ->  FldComElt, SeqEnum[FldComElt], SeqEnum[CPath], SeqEnum[SeqEnum[RngIntElt]], SeqEnum[FldReElt]
{ Computes a generating set for the fundamental group Pi_1(C - Points,x_0) of the punctured complex plane with a basepoint x_0. }

	CC<I> := Universe(Points);
	Points := SetToSequence(Set(Points));
	d := #Points;

	/* Dealing with special cases */
	if d eq 0 then
		return Zero(CC), [], [], [];
	elif d eq 1 then
		BasePoint := Points[1] - MaxSafeRadius;
		return BasePoint, Points, [ CFullCircle(BasePoint, Points[1]) ], [[1]], [MaxSafeRadius];
	end if;

	/* Low precision discriminant points */
	LPDP := ChangeUniverse(Points,ComplexField(Min(30,Precision(CC))));

	vprint RS,1 : "Choosing suitable basepoint..";
	if Type(BasePoint) eq MonStgElt then
		require BasePoint in ["Left","Clever"] : "Invalid base point.";
		if BasePoint eq "Left" then
			MinRe, Ind := Min([Re(z) : z in Points]);
			BP := CC!Floor(Min(MinRe - 2*MaxSafeRadius, -1));
		end if;
	else
		/* User-specified basepoint */
		if IsCoercible(CC,BasePoint) then
			BP := CC!BasePoint;
			BasePoint := "User";
		else	
			error Error("Basepoint must be coercible into complex field.");
		end if;
	end if;

	/* Compute minimal spanning tree w.r.t euclidean distance */
	MST_Edges := MinimalSpanningTree(LPDP);

	if BasePoint eq "Clever" then
		MaxDist, MaxInd := Max( [ Abs(Points[E[1]]-Points[E[2]]) : E in MST_Edges ] );
		Paths := [ CLineSegment( Points[MST_Edges[j][1]],Points[MST_Edges[j][2]] ) : j in Remove([1..d-1],MaxInd) ];
		BP := (Points[MST_Edges[MaxInd][1]]+Points[MST_Edges[MaxInd][2]])/2;
		Insert(~Paths,1,CLineSegment(BP,Points[MST_Edges[MaxInd][1]]));
		Insert(~Paths,1,CLineSegment(BP,Points[MST_Edges[MaxInd][2]]));
	else
		Dist, Ind := Distance(BP,Points);
		Paths := [ CLineSegment( Points[MST_Edges[j][1]],Points[MST_Edges[j][2]] ) : j in [1..d-1] ];
		Insert(~Paths,1,CLineSegment(BP,Points[Ind]));
	end if;

	/* Assumed here: BP = Paths[1]`StartPt */
	PathPieces := FormatedMST(Paths,Points);		

	OrdDiscPoints := []; 
	InitialPath := [CPoint(BP)];
	Paths := [];
	FindPathsWithDFS( ~OrdDiscPoints, ~InitialPath, ~Paths, PathPieces );
	for j in [1..#Paths] do
		Remove(~Paths[j],1);
	end for;
	IndexPathLists := [];	
	for Path in Paths do
		IndexPathList := [];
		for Gamma in Path do
			Append(~IndexPathList, Position(PathPieces, Gamma));
		end for;
		Append(~IndexPathLists, IndexPathList);
	end for;

	/* Compute safe radii again (after sorting discriminant points!) */
	SafeRadii := [ Min(MaxSafeRadius,SafeRadiusFactor*Distance(OrdDiscPoints[j],Remove(OrdDiscPoints,j))) : j in [1..d] ];

	/* Extend spanning tree using arcs and circles */
	PathPieces, IndexPathLists := MSTtoMSTX(PathPieces,IndexPathLists);
	
	return BP, OrdDiscPoints, PathPieces, IndexPathLists, SafeRadii;
end intrinsic;

intrinsic DiscriminantPoints( f::RngMPolElt ) ->  SeqEnum[FldComElt]
{ Computes the complex roots of the discriminant of f in Q[x,y] in the y. }
	K := BaseRing(Parent(f));
	require K eq Rationals() : "Polynomial has to be defined over the rationals";
	K := RationalsAsNumberField();
	f := ChangeRing(f,K);
	sigma := InfinitePlaces(K)[1];
	return DiscriminantPoints(f,sigma);
end intrinsic;
intrinsic DiscriminantPoints( f::RngMPolElt, sigma::PlcNumElt ) ->  SeqEnum[FldComElt]
{ Computes the complex roots of the discriminant of f in K[x,y] in the y using the embedding sigma. }
	Kxy := Parent(f);
	require Rank(Kxy) eq 2 : "Input has to be a polynomial in two variables.";
	K := BaseRing(Kxy);
	require Type(K) eq FldNum : "Polynomial has to be defined over a number field.";
	require IsInfinite(sigma) : "PlcNumElt has to be infinite";
	Fact1 := Factorization(UnivariatePolynomial(Discriminant(f,Kxy.2)));
	LC := UnivariatePolynomial(LeadingCoefficient(f,Kxy.2));
	LCLC := LeadingCoefficient(LC);
	Fact2 := Factorization(LC);
	vprint RS,2 : "Fact(Disc):",Fact1;
	vprint RS,2 : "Fact(LC):",Fact2;
	/* Initial discriminant points to precision 200 */
	C200<w> := PolynomialRing(ComplexField(200));
	DP1 := {};
	for j in [1..#Fact1] do
		Rts1 := Roots(EmbedPolynomial(Fact1[j][1],sigma,C200));
		DP1 join:= Set([rt[1] : rt in Rts1 ]);
	end for;
	DP2 := {};
	for j in [1..#Fact2] do
		Rts2 := Roots(EmbedPolynomial(Fact2[j][1],sigma,C200));
		DP2 join:= Set([rt[1] : rt in Rts2 ]);
	end for;
	DP := SetToSequence(DP2 join DP1);
	NDP2 := #DP2;
	vprint RS,3 : "DP1:",DP1;
	vprint RS,3 : "DP2:",DP2;
	/* Bound Y-Values */
	R10 := RealField(10);
	XB := R10!Max([Abs(Pt) : Pt in DP ]) + MaxSafeRadius;
	vprint RS,2 : "Maximal Abs(x):",XB;
	if #DP2 eq 0 then
		L0SafeRadius := One(R10);
	else
		DP2Dist := Min([ Distance(Pt,Remove(DP,Position(DP,Pt))) : Pt in DP2 ]);
		vprint RS,2 : "DP2Dist:",ChangePrecision(DP2Dist,10);
		L0SafeRadius := Min(SafeRadiusFactor*DP2Dist,MaxSafeRadius);
	end if;
	vprint RS,2 : "L0MinSafeRadius:",ChangePrecision(L0SafeRadius,10);
	
	/* Bound |x|,|y| */
	C20f := EmbedPolynomial(f,sigma,PolynomialRing(ComplexField(20),2));

	/* Bounds |y(x)| on f(x,y) = 0 for |x| < xb and |x-x_0| > dist for all zeros x_0 of LC */
	function BoundYValues(xb,dist)
		Cffs_y := Reverse(Coefficients(C20f,2));
		Cffs_y := [ UnivariatePolynomial(c) : c in Cffs_y ];
		MaxYAbs := 0; MaxXAbs := 0;
		for k in [1..Degree(f,Kxy.2)] do
			Cffs_x := Coefficients(Cffs_y[k+1]);
			if #Cffs_x gt 0 then
				Ak := &+[ Abs(Cffs_x[j]) * xb^(j-1) : j in [1..#Cffs_x] ];
				MaxYAbs := Max(MaxYAbs,Ak/(Abs(Evaluate(LCLC,sigma))*dist^Degree(LC))^(1/k));
				MaxXAbs := Max(MaxXAbs,Ak);
			end if;
		end for;
		return Max(2*MaxYAbs,MaxXAbs);
	end function;
	YB := BoundYValues(XB,(100/101)*L0SafeRadius);
	vprint RS,2 : "YB:",YB;

	/* Heuristic extra digits */
	ExtraDigits := Ceiling(Log(10,YB));
	vprint RS,2 : "ExtraDigits:",ExtraDigits;
	MaxPrec := Max(ExtraDigits,40);
	vprint RS,1 : "Maximal precision (estimated):",MaxPrec;
	CC<I> := ComplexField(MaxPrec);
	CCw<w> := PolynomialRing(CC);
	if Precision(CC) gt 200 then
		DP := {};
		for j in [1..#Fact1] do
			Rts1 := Roots(EmbedPolynomial(Fact1[j][1],sigma,CCw));
			DP join:= Set([rt[1] : rt in Rts1 ]);
		end for;
		for j in [1..#Fact2] do
			Rts2 := Roots(EmbedPolynomial(Fact2[j][1],sigma,CCw));
			DP join:= Set([rt[1] : rt in Rts2 ]);
		end for;
		DP := ChangeUniverse(SetToSequence(DP),CC);
	else
		DP := ChangeUniverse(DP,CC);
	end if;
	/* Clean-up entries */
	WeakError := Real(10^-Round((Precision(CC)/2)));
	for k in [1..#DP] do
		r := DP[k];
		if Abs(Re(r)) lt WeakError then
			DP[k] := CC.1 * Im(r);
		end if;
		if Abs(Im(r)) lt WeakError then
			DP[k] := Re(r);
		end if;	
	end for;
	DP := SetToSequence(Set(DP));
	return Sort(DP,CompareFldComElt), [XB,YB], BoundYValues;
end intrinsic;

function InternalDiscriminantPoints( X )
/* Computes the roots of the discriminant of f in the variable z \in [x,y] */
	//Kxy := Parent(X`DefiningPolynomial);
	Kxy := Parent(X`AffineModel); 
	K := BaseRing(Kxy);
	Fact1 := Factorization(UnivariatePolynomial(Discriminant(X`DefiningPolynomial,2)));
	LC := UnivariatePolynomial(LeadingCoefficient(X`DefiningPolynomial,2));
	LCLC := LeadingCoefficient(LC);
	Fact2 := Factorization(LC);
	vprint RS,2 : "Fact(Disc):",Fact1;
	vprint RS,2 : "Fact(LC):",Fact2;

	/* Initial discriminant points to precision 200 */
	C200<w> := PolynomialRing(ComplexField(200));
	DP1 := {};
	for j in [1..#Fact1] do
		Rts1 := Roots(EmbedPolynomial(Fact1[j][1],X`Embedding,C200));
		DP1 join:= Set([rt[1] : rt in Rts1 ]);
	end for;
	DP2 := {};
	for j in [1..#Fact2] do
		Rts2 := Roots(EmbedPolynomial(Fact2[j][1],X`Embedding,C200));
		DP2 join:= Set([rt[1] : rt in Rts2 ]);
	end for;
	DP := SetToSequence(DP2 join DP1);
	NDP2 := #DP2;
	vprint RS,3 : "DP1:",DP1;
	vprint RS,3 : "DP2:",DP2;

	/* Bound Y-Values */
	R10 := RealField(10);
	XB := R10!Max([Abs(Pt) : Pt in DP ]) + MaxSafeRadius;
	vprint RS,2 : "Maximal Abs(x):",XB;
	if #DP2 eq 0 then
		L0SafeRadius := One(R10);
	else
		DP2Dist := Min([ Distance(Pt,Remove(DP,Position(DP,Pt))) : Pt in DP2 ]);
		vprint RS,2 : "DP2Dist:",DP2Dist;
		L0SafeRadius := Min(SafeRadiusFactor*DP2Dist,MaxSafeRadius);
	end if;
	vprint RS,2 : "L0MinSafeRadius:",L0SafeRadius;
	
	/* Bound |x|,|y| */
	C20f := EmbedPolynomial(X`DefiningPolynomial,X`Embedding,PolynomialRing(ComplexField(20),2));

	/* Bounds |y(x)| on f(x,y) = 0 for |x| < xb and |x-x_0| > dist for all zeros x_0 of LC */
	function BoundYValues(xb,dist)
		Cffs_y := Reverse(Coefficients(C20f,2));
		Cffs_y := [ UnivariatePolynomial(c) : c in Cffs_y ];
		MaxYAbs := 0; MaxXAbs := 0;
		for k in [1..X`Degree[1]] do
			Cffs_x := Coefficients(Cffs_y[k+1]);
			if #Cffs_x gt 0 then
				Ak := &+[ Abs(Cffs_x[j]) * xb^(j-1) : j in [1..#Cffs_x] ];
				MaxYAbs := Max(MaxYAbs,Ak/(Abs(Evaluate(LCLC,X`Embedding))*dist^Degree(LC))^(1/k));
				MaxXAbs := Max(MaxXAbs,Ak);
			end if;
		end for;
		return Max(2*MaxYAbs,MaxXAbs);
	end function;
	YB := BoundYValues(XB,(100/101)*L0SafeRadius);
	vprint RS,2 : "YB:",YB;

	/* Bound differentials (heuristically) */
	if X`Baker then
		dfy := EmbedPolynomial(X`HolomorphicDifferentials[2],X`Embedding,PolynomialRing(ComplexField(20),2));
		MaxDiffAbs := [ Max(1,Abs(Evaluate(dfy,ChangeUniverse([XB,YB],BaseRing(Parent(dfy)))))) ];
		OneVec := [ XB^s[1] * YB^s[2] : s in X`HolomorphicDifferentials[1] ]; 
	else
		DFF := X`HolomorphicDifferentials;
		MaxDiffAbs := [ R10 | ];
		for k in [1..#DFF[5]] do
			g := DFF[5][k];
			Cffs := Coefficients(g);
			Mms := Monomials(g);
			Val := Abs(&+[ Abs(Cffs[j]) * Evaluate(Mms[j],[XB,YB]) : j in [1..#Cffs] ]);
			Append(~MaxDiffAbs,Max(Val,1));
		end for;
		OneVec := [ One(R10) : j in [1..X`Genus]];
		for l in [1..#DFF[1]] do
			val := MaxDiffAbs[l];
			Fac_xys := [ R10 | ];
			for k in [0..DFF[4][l]] do
				if DFF[3][l]+k le 0 then
					Fac_xys[k+1] := 1;
				else
					Fac_xys[k+1] := MaxDiffAbs[l]^(DFF[3][l]+k);
				end if;
			end for;
			for k in [1..X`Genus] do
				OneVec[k] *:= Fac_xys[DFF[2][l][k]-DFF[3][l]+1];
			end for;
		end for;
	end if;
	vprint RS,2 : "Bounds(Factors):",MaxDiffAbs;
	vprint RS,2 : "Bounds(Differentials):",OneVec;
	Bound := Max(Append(MaxDiffAbs,YB) cat OneVec);
	
	// Heuristic extra digits
	
	//Bound := YB;
	ExtraDigits := Ceiling(Log(10,Bound));
	vprint RS,2 : "ExtraDigits:",ExtraDigits;
	MaxPrec := Precision(X`ComplexFields[2]) + Max(ExtraDigits,20);
	vprint RS,1 : "Maximal precision (estimated):",MaxPrec;
	Append(~X`ComplexFields,ComplexField(MaxPrec));

	CC<I> := ComplexField(X`Degree[1]*MaxPrec);	
	Append(~X`ComplexFields,CC);
	CCw<w> := PolynomialRing(CC);
	if Precision(CC) gt 200 then
		DP := {};
		for j in [1..#Fact1] do
			Rts1 := Roots(EmbedPolynomial(Fact1[j][1],X`Embedding,CCw));
			DP join:= Set([rt[1] : rt in Rts1 ]);
		end for;
		for j in [1..#Fact2] do
			Rts2 := Roots(EmbedPolynomial(Fact2[j][1],X`Embedding,CCw));
			DP join:= Set([rt[1] : rt in Rts2 ]);
		end for;
		DP := SetToSequence(DP);
	end if;
	
	/* Clean-up entries */
	for k in [1..#DP] do
		r := DP[k];
		if Abs(Re(r)) lt X`WeakError then
			DP[k] := CC.1 * Im(r);
		end if;
		if Abs(Im(r)) lt X`WeakError then
			DP[k] := Re(r);
		end if;	
	end for;
	vprint RS,2 : "Universe of discriminant points:",Universe(DP);
	return Sort(DP,X`Ordering), [XB,YB,Bound], BoundYValues;
end function;

/* Fundamental group for superelliptic Riemann surfaces -> Spanning tree */

/* Define edge type for superelliptic Riemann surfaces */
declare type SEEdge;

declare attributes SEEdge :
	EP, // End points = [E1,E2]
	Data, // Data = [ u_1, ... , u_{n-2},(b-a)/2,(b+a)/(b-a),C_ab ]
	up, 
	r, // Integration parameter
	Vr,
	Isgn,
	IntSch, // Which integration scheme?
	IntMethod, // Which integration method?
	vp; // Multiplicity for Abel-Jacobi

intrinsic Print( E::SEEdge )
{ Printing. }
	print "Edge:",E`EP;
end intrinsic;

/* Constructor for edges */
function SE_Edge(k,l:r:=0)
	E := New(SEEdge);
	if Type(l) eq RngIntElt then
		E`EP := [k,l];
	elif Type(l) eq SeqEnum then
		E`EP := <k,l>;
	else
		error Error("Not supposed to happen.");
	end if;
	if r ne 0 then
		E`r := r;
	end if;
	return E;
end function;
function ImSgn(z)
	if IsReal(z) then return 1; else return Sign(Im(z)); end if;
end function;
procedure EdgeData( E,Points,Zetas,m,n )
	a := Points[E`EP[1]];
	if Type(E`EP[2]) eq RngIntElt then
		b := Points[E`EP[2]];
		if E`EP[1] lt E`EP[2] then
			Pts := Remove(Remove(Points,E`EP[1]),E`EP[2]-1);
		else
			Pts := Remove(Remove(Points,E`EP[2]),E`EP[1]-1);
		end if;
		bpa := b+a; bma := b-a; bmainv := 1/bma;
		CCV, up := SortByRealPart([ (2*x-bpa)*bmainv : x in Pts ]);
		E`Isgn := [ ImSgn(CCV[k]) : k in [1..up] ] cat [ -ImSgn(CCV[k]) : k in [up+1..n-2] ];
		Append(~CCV,bma/2);
		Append(~CCV,(b+a)/bma);
		if IsReal(bma) and Real(bma) lt 0 then
			/* Fix Magma here: Log(-R) inconsistent! */
			C<I> := Universe(Points);
			C_ab := Exp( (n/m) * (Log(-bma)+I*Pi(C))) * Zetas[(up+1) mod 2 + 1];
		else
			C_ab := Exp( (n/m) * Log(bma)) * Zetas[(up+1) mod 2 + 1];
		end if;
		Append(~CCV,C_ab);
	elif Type(E`EP[2]) eq SeqEnum then
		b := E`EP[2][1];
		Pts := Remove(Points,E`EP[1]);
		bpa := b+a; bma := b-a; bmainv := 1/bma;
		CCV, up := SortByRealPart([ (2*x-bpa)*bmainv : x in Pts ]);
		E`Isgn := [ ImSgn(CCV[k]) : k in [1..up] ] cat [ -ImSgn(CCV[k]) : k in [up+1..n-1] ];
		Append(~CCV,bma/2);
		Append(~CCV,(b+a)/bma);
	else
		error Error("Not supposed to happen.");
	end if;
	E`up := up;
	E`Data := CCV;
end procedure;

procedure FlipEdge( E )
	E`EP := Reverse(E`EP);
end procedure;

/* Compare r-value of edges */
function CompareEdge( E1,E2 )
	if E1`r le E2`r then
		return 1;
	else
		return -1;
	end if;
end function;

/* Weights for edges in spanning tree */
function DE_Weight( P1,P2,P3 : Lambda := RPI/2 )
	z := (2*P3 - P2 - P1) / (P2 - P1);
	return Abs(Im(Argsinh(Argtanh(z)/Lambda)));
end function;
procedure DE_Edge_Weight( ~Edge, Points, Len : Lambda := RPI/2 )
	CCV := [];
	for k in [1..Len] do
		if k notin Edge`EP then
			uk := (2*Points[k] - Points[Edge`EP[2]] - Points[Edge`EP[1]]) / (Points[Edge`EP[2]] - Points[Edge`EP[1]]);
			Append(~CCV,uk);
			Edge`r := Min(Edge`r,Abs(Im(Argsinh(Argtanh(uk)/Lambda))));
		end if;
	end for;
	Edge`Data := CCV;
end procedure;
procedure GJ_Edge_Weight( ~Edge, Points, Len )
	V_r := [];
	for k in [1..Len] do
		if k notin Edge`EP then
			uk := (2*Points[k] - Points[Edge`EP[2]] - Points[Edge`EP[1]]) / (Points[Edge`EP[2]] - Points[Edge`EP[1]]);
			rk := (Abs(uk+1) + Abs(uk-1))/2;
			Append(~V_r,rk);
		end if;
	end for;
	Edge`Data := V_r;
	Edge`r := Min(Append(V_r,5.0));
end procedure;
/* Weights for edges in Abel-Jacobi map */
procedure DE_AJM_Weight( ~Edge, Len : Lambda := RPI/2 )
	Edge`r := 5.0;
	for k in [1..Len] do
		Edge`r := Min(Edge`r,Abs(Im(Argsinh(Argtanh(Edge`Data[k])/Lambda))));
	end for;
end procedure;
procedure GJ_AJM_Weight( ~Edge, Len )
	Edge`Vr := [ 5.0];
	for k in [1..Len] do
		P := ChangePrecision(Edge`Data[k],30);
		Append(~Edge`Vr,(Abs(P+1) + Abs(P-1))/2);
	end for;
	Edge`r := Min(Edge`Vr);
	Remove(~Edge`Vr,1);
end procedure;

function GJ_Params_Tree(Edges,m,n)
/* Compute Gauss-Jacobi integration parameters for a spanning tree */
	NE := #Edges;
	IntPars := Sort([ Edges[k]`r : k in [1..NE] ]);
	rm := IntPars[1];
	Groups := IntGroups_SE(IntPars,rm,m);
	vprint RS,2 : "Groups:",Groups;
	eps := 1/500;
	if rm lt 1+(1/250) then
		Lr := [(1/2)*(rm+1)]; 
	else
		Lr := [ rm - eps];
	end if;
	if m eq 2 then
		Lr cat:= [ Min(g) - eps : g in Remove(Groups,1) | #g gt 1 ];
	else
		Lr cat:= [ Min(g) - eps : g in Remove(Groups,1) | #g gt 2 ];
	end if;

	/* Find best integration scheme for each edge and compute bound M(r) */
	NSchemes := #Lr;
	LrM := [ <1,Lr[l]> : l in [1..NSchemes] ];
	for k in [1..NE] do
		M := 1;
		l := Max([ l : l in [1..NSchemes] | Edges[k]`r gt Lr[l] ]);
		Edges[k]`IntSch := l;
		M := Exp( -(1/m) * Log( &*[ Edges[k]`Data[j] - Lr[l] : j in [1..n-2]]));
		if M ge 1 then
			M := M^(m-1);
		end if;
		M := Ceiling(Lr[l]^(n-2) * M);
		LrM[l][1] := Max(M,LrM[l][1]);
	end for;
	return LrM;
end function;

function GJ_Params_AJM(NewEdges,m,n)
/* Compute parameters for Gauss-Jacobi integration for Abel-Jacobi map edges */
	NE := #NewEdges;
	IntPars := Sort([ NewEdges[k]`r : k in [1..NE] ]);
	rm := IntPars[1];
	Groups := IntGroups_SE(IntPars,rm,m);
	vprint RS,2 : "Groups:",Groups;
	eps := 1/500;
	if rm lt 1+(1/250) then
		Lr := [(1/2)*(rm+1)]; 
	else
		Lr := [ rm - eps];
	end if;
	Lr cat:= [ Min(g) - eps : g in Remove(Groups,1) | #g gt 2 ];

	/* Find best integration scheme for each edge and compute bound M(r) */
	NSchemes := #Lr;
	LrM := [ <1,Lr[l]> : l in [1..NSchemes] ];
	for k in [1..NE] do
		l := Max([ l : l in [1..NSchemes] | NewEdges[k]`r gt Lr[l] ]);
		NewEdges[k]`IntSch := l;
		M := Exp( -(1/m) * Log( &*[ NewEdges[k]`Vr[j] - Lr[l] : j in [1..n-1]]));
		if M ge 1 then
			M := M^(m-1);
		end if;
		M := Ceiling(Lr[l]^(n-2) * M);
		LrM[l][1] := Max(M,LrM[l][1]);
	end for;
	vprint RS,2 : "Parameters(GJ,AJM):",LrM;
	return LrM;
end function;

function DE_Params_Tree(Edges,m,n)
/* Computes double-exponential integration integration parameters for a spanning tree */
	NE := #Edges;
	IntPars := Sort([ Edges[k]`r : k in [1..NE] ]);
	rmi := IntPars[1]; rma := IntPars[NE];
	NSchemes := Max(Ceiling(20*(rma-rmi)),1);
	Groups := [ [] : j in [1..NSchemes] ];
	for r in IntPars do
		t := Max(Ceiling(20*(r-rmi)),1);
		Append(~Groups[t],r);
	end for;
	vprint RS,2 : "Groups:",Groups;
	Lr := [ (29/30) * rmi ] cat [ (29/30) * Min(g) : g in Remove(Groups,1) | #g gt 1 ];
	NSchemes := #Lr;
	vprint RS,2 : "Number of schemes:",NSchemes;
	assert &and[rma lt RPI/2, rmi gt 0];

	/* Find best integration scheme for each edge and compute bounds M1, M2 */
	NSchemes := #Lr; 
	LrM := [ <1,1,Lr[l]> : l in [1..NSchemes] ];
	for k in [1..NE] do
		l := NSchemes;
		while Edges[k]`r lt Lr[l] do
			l -:= 1;
		end while;
		Edges[k]`IntSch := l;
		M1 := Ceiling(Bound_M1(Edges[k]`Data,n-2,m));
		M2 := Ceiling(Bound_M2(Edges[k]`Data,n-2,m,n,Lr[l]));
		LrM[l][1] := Max(M1,LrM[l][1]);
		LrM[l][2] := Max(M2,LrM[l][2]);
	end for;
	return LrM;
end function;

function DE_Params_AJM(NewEdges,m,n)
/* Computes double-exponential integration integration parameters for Abel-Jacobi map edges */
	NE := #NewEdges;
	IntPars := Sort([ NewEdges[k]`r : k in [1..NE] ]);
	rmi := IntPars[1]; rma := IntPars[NE];
	NSchemes := Max(Ceiling(20*(rma-rmi)),1);
	Groups := [ [] : j in [1..NSchemes] ];
	for r in IntPars do
		t := Max(Ceiling(20*(r-rmi)),1);
		Append(~Groups[t],r);
	end for;
	vprint RS,2 : "Groups:",Groups;
	Lr := [ (29/30) * rmi ] cat [ (29/30) * Min(g) : g in Remove(Groups,1) | #g gt 1 ];
	NSchemes := #Lr;
	vprint RS,2 : "Number of schemes:",NSchemes;
	assert &and[rma lt RPI/2, rmi gt 0];

	/* Find best integration scheme for each edge and compute bounds M1, M2 */
	NSchemes := #Lr; 
	LrM := [ <1,1,Lr[l]> : l in [1..NSchemes] ];
	for k in [1..NE] do
		l := NSchemes;
		while NewEdges[k]`r lt Lr[l] do
			l -:= 1;
		end while;
		NewEdges[k]`IntSch := l;
		M1 := Ceiling(Bound_M1(NewEdges[k]`Data,n-1,m:AJM));
		M2 := Ceiling(Bound_M2(NewEdges[k]`Data,n-1,m,n,Lr[l]:AJM));
		LrM[l][1] := Max(M1,LrM[l][1]);
		LrM[l][2] := Max(M2,LrM[l][2]);
	end for;
	vprint RS,2 : "Parameters(DE,AJM):",LrM;
	return LrM;
end function;

procedure Mixed_Params_Tree(X)
/* Parameters for mixed integration schemes */
	m := X`Degree[1];
	n := X`Degree[2];
	Points := X`LPDP;
	X`SpanningTree`DE_Params := [];
	X`SpanningTree`GJ_Params := [];	
	if X`IntMethod eq "Mixed" then
		if m eq 2 then
			cst := 1.005;
		else
			cst := 2.0;
		end if;
		DE_Edges := []; GJ_Edges := [];
		for k in [1..n-1] do
			E := X`SpanningTree`Edges[k];
			if E`r lt cst then
				E`r := 5.0;
				DE_Edge_Weight(~E,Points,n);
				E`IntMethod := "DE";
				Append(~DE_Edges,E);
			else
				Append(~GJ_Edges,E);
			end if;
		end for;
		X`SpanningTree`GJ_Params := GJ_Params_Tree(GJ_Edges,m,n);
		NrGJInts := #X`SpanningTree`GJ_Params;
		if #DE_Edges gt 0 then
			X`SpanningTree`DE_Params := DE_Params_Tree(DE_Edges,m,n);
		end if;
	elif X`IntMethod eq "GJ" then
		X`SpanningTree`GJ_Params := GJ_Params_Tree(X`SpanningTree`Edges,m,n);
	elif X`IntMethod eq "DE" then
		X`SpanningTree`DE_Params := DE_Params_Tree(X`SpanningTree`Edges,m,n);
	else 
		error Error("Integration method not supported.");
	end if;
end procedure;
function Mixed_Params_AJM(ComplexEdges,X)
/* Parameters for mixed integration schemes Abel-Jacobi map */
	m := X`Degree[1];
	n := X`Degree[2];
	NEdges := #ComplexEdges; 
	DE_Edges := []; GJ_Edges := [];
	if X`IntMethod eq "Mixed" then
		cst := 2.0;
		for j in [1..NEdges] do
			E := ComplexEdges[j];
			GJ_AJM_Weight(~E,n-1);
			if E`r lt cst then
				E`r := 5.0;
				DE_AJM_Weight(~E,n-1);
				E`IntMethod := "DE";
				Append(~DE_Edges,E);
			else
				E`IntMethod := "GJ";
				Append(~GJ_Edges,E);
			end if;
		end for;
		if #GJ_Edges gt 0 then
			GJ_Params := GJ_Params_AJM(GJ_Edges,m,n);
		else
			GJ_Params := [];
		end if;
		if #DE_Edges gt 0 then
			DE_Params := DE_Params_AJM(DE_Edges,m,n);
		else
			DE_Params := [];
		end if;
	elif X`IntMethod eq "GJ" then
		for j in [1..NEdges] do
			E := ComplexEdges[j];
			GJ_AJM_Weight(~E,n-1);
			E`IntMethod := "GJ";
			Append(~GJ_Edges,E);
		end for;
		GJ_Params := GJ_Params_AJM(GJ_Edges,m,n); DE_Params := [];
	elif X`IntMethod eq "DE" then
		for j in [1..NEdges] do
			E := ComplexEdges[j];
			DE_AJM_Weight(~E,n-1);
			E`IntMethod := "DE";
			Append(~DE_Edges,E);
		end for;
		DE_Params := DE_Params_AJM(DE_Edges,m,n); GJ_Params := [];
	else 
		error Error("Integration method not supported.");
	end if;
	return GJ_Params, DE_Params, GJ_Edges, DE_Edges;
end function;


/* SpTree: spanning tree type for superelliptic Riemann surfaces */
declare type SpTree;
declare attributes SpTree :
	Length,
	Edges,
	DE_Params,
	GJ_Params;
procedure TreeData( ~SpTree, Points, Zetas, m )
/* Computes all data necessary for a period matrix computation */
	for E in SpTree`Edges do
		EdgeData(E,Points,Zetas,m,SpTree`Length+1);
	end for;
end procedure;
procedure SpanningTree(X)
/* Computes a spanning tree between the branch points */
	Points := X`LPDP;	
	Len := X`Degree[2];
	Edges := [];
	T := New(SpTree);
	T`Length := Len-1;
	T`Edges := [];
	Min_r := 5.; Max_r := 0.;	

	/* Make edges and weights (euclidean distance) */ 
	for k in [1..Len] do
		for l in [k+1..Len] do
			Append(~Edges,SE_Edge(k,l:r:=-Abs(Points[k]-Points[l])));
		end for;
	end for;
	/* Sort by third entry */
	Sort(~Edges,CompareEdge);

	Taken := [ 0 : j in [1..Len] ];
	k := 0;
	while k lt T`Length do
		l := 1;
		if k ne 0 then
			while Taken[Edges[l]`EP[1]] eq Taken[Edges[l]`EP[2]] do
				l +:= 1;
			end while;
		end if;
		NewEdge := SE_Edge(Edges[l]`EP[1],Edges[l]`EP[2]:r:=5.);
		if X`IntMethod eq "DE" then
			DE_Edge_Weight(~NewEdge,Points,Len);
			NewEdge`IntMethod := "DE";
		else
			GJ_Edge_Weight(~NewEdge,Points,Len);
			NewEdge`IntMethod := "GJ";
		end if;
		if Taken[NewEdge`EP[2]] eq 1 then
			FlipEdge(NewEdge);
		end if;
		Append(~T`Edges,NewEdge);
		k +:= 1;
		Taken[NewEdge`EP[1]] := 1;
		Taken[NewEdge`EP[2]] := 1;
	end while;
	X`SpanningTree := T;	
end procedure;
intrinsic Print( STree::SpTree )
{ Printing. }
	print "Spanning tree between",STree`Length+1,"points";
	print "with edges:",STree`Edges;
	if assigned STree`DE_Params then
		print "Integration parameters (DE):",STree`DE_Params;
	end if;
	if assigned STree`GJ_Params then
		print "Integration parameters (GJ):",STree`GJ_Params;
	end if;
end intrinsic;

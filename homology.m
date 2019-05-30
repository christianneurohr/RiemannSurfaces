/*******************************************************************************

	Homology basis for Riemann surfaces
 
	Christian Neurohr, June 2019

*******************************************************************************/

import "integration.m": AC_mthRoot;
import "miscellaneous.m": MakeCCVector;

/* Start type RSEdge : suitable edge class for Tretkoff algorithm */
declare type RSEdge;
declare attributes RSEdge: StPt, EndPt, Branch, Level, Terminated, Position, PQ;

/* Printing for Tretkoff */
declare verbose Tretkoff,2;

/* Constructor: creates an RSEdge */
function MakeEdge( E : Branch := [E[1],E[2]], Level := 0, Terminated := false )
	e := New(RSEdge);
	e`StPt := E[1]; e`EndPt := E[2];
	e`Branch := Branch;
	e`Level := Level;
	e`Terminated := Terminated;
	if e`StPt lt e`EndPt then
		e`PQ := true;
	else
		e`PQ := false;
	end if;
	return e;
end function;

intrinsic Print( e::RSEdge )
{ Prining. }
	if e`Terminated then
		print "Edge from",e`StPt,"to",e`EndPt,"on Level",e`Level,"and Terminated Branch",e`Branch;
	else
		print "Edge from",e`StPt,"to",e`EndPt,"on Level",e`Level,"and Branch",e`Branch;
	end if;
end intrinsic;

/* Define "=" on RSEdges */
intrinsic 'eq'( E1::RSEdge, E2::RSEdge ) -> BoolElt
{ Returns true if E1 = E2, false otherwise }
	return (E1`StPt eq E2`StPt) and (E1`EndPt eq E2`EndPt);
end intrinsic;

function ReverseEdge(Edge)
/* Returns the edge with swapped start- and end point */
	return MakeEdge(<Edge`EndPt,Edge`StPt>);
end function;
/* End type : RSEdge */

function CycleToPerm(Tau,m)
/* Creates a permutation element from the indexed set Tau */
	Perm := [1..m];
	t := #Tau;
	for j in [1..t] do
		Perm[Tau[j]] := Tau[j mod t + 1];
	end for;
	return Sym(m)!Perm;
end function;

/* Functions for sorting edges */

function SortTermEdges(EdgesOnPartLevel, StOrEnd)
/* Sorts the terminated edges in step 3 and 5. If StOrEnd = -1 sort by increasing start point,
 if StOrEnd = 1 sort by increasing end point */
	function CompareEdges( Edge1, Edge2 )
		if StOrEnd eq -1 then
			e1 := Edge1`StPt; e2 := Edge2`StPt;
		else
			e1 := Edge1`EndPt; e2 := Edge2`EndPt;
		end if;
		if e1 lt e2 then 
			return -1;
		elif e1 eq e2  then 
			if Edge1`Position lt Edge2`Position then	
				return -1;
			elif Edge1`Position eq Edge2`Position then	
				return 0;
			else
				return 1;
			end if;
		else 
			return 1; 
		end if;
	end function;
	return Sort(EdgesOnPartLevel,CompareEdges);
end function;

function SortByBranch( EdgesOnLevel, TerminatedEdges )
/* Returs the list of terminated edges sorted by using CompareBranches */
	function CompareBranches(Edge1,Edge2)
		/* Edge1 < Edge2 iff Edge1 appears earlier while going counter-clockwise through the Tretkoff tree
		   Edge2 > Edge2 iff Edge2  --- "" --- */
		if Edge1`Level eq Edge2`Level then
			if Edge1`Position lt Edge2`Position then	
				return -1;
			elif Edge1`Position eq Edge2`Position then	
				return 0;
			else
				return 1;
			end if;
		elif Edge1`Level lt Edge2`Level then
			PredEdge2 := MakeEdge(<Edge2`Branch[Edge1`Level],Edge2`Branch[Edge1`Level+1]>);
			Ind := Position(EdgesOnLevel[Edge1`Level],PredEdge2);
			return CompareBranches(Edge1,EdgesOnLevel[Edge1`Level][Ind]);
		else
			return (-1)*CompareBranches(Edge2,Edge1);
		end if;
	end function;
	return Sort(TerminatedEdges,CompareBranches);	
end function;

/* Tretkoff algorithm starts here! */

intrinsic HomologyBasis( LocalMonodromy::SeqEnum[GrpPermElt] ) -> SeqEnum[SeqEnum[RngIntElt]], Mtrx
{ Compute a basis of the first homology group of a connected compact Riemann surface from a monodromy representation using an algotihm
 by Tretkoff & Tretkoff. }

	d := #LocalMonodromy;
	if d eq 0 then
		error Error("Input cannot be an empty list.");
	else
		Sym := Universe(LocalMonodromy);
		m := Degree(Sym);
	end if;
	
	// Checking connectivity of the Riemann surface
	S := PermutationGroup< m | [ s : s in LocalMonodromy ] >;
	assert IsTransitive(S);

	// Decompose the local monodromies into disjoint cycles
	RamificationPoints := []; RamificationIndices := [];
	for j in [1..d] do
		CycleDecomp := CycleDecomposition(LocalMonodromy[j]);
		for Tau in CycleDecomp do
			if #Tau gt 1 then
				Append(~RamificationPoints,<j,Tau,CycleToPerm(Tau,m)>);
				Append(~RamificationIndices,#Tau-1);
			end if;
		end for;
	end for;

	vprint Tretkoff,1 : "Ramification points:",RamificationPoints;
	vprint Tretkoff,1 : "Ramification indices:",RamificationIndices;

	// Checking Riemann-Hurwitz formula
	GenusViaMonodromy := 1/2 * &+RamificationIndices + 1 - m;
	Ok, g := IsCoercible(Integers(),GenusViaMonodromy);
	if not Ok or g lt 0 then
		error Error("Riemann-Hurwitz formula violated.");
	end if;

	// Dealing with genus 0 curves
	if g eq 0 then
		error Error("Genus of the Riemann surface is zero; Homology group is trivial.");
	else	
		vprint Tretkoff,1 : "Genus of the Riemann surface: ",g;
	end if;
	
	// Initializing Tretkoff tree
	// Vertices 1,...,t correspond to ramification points
	// Vertices t+1,...,t+m correspond to sheets
	t := #RamificationPoints;
	Vertices := {t+1};
	EdgesOnLevel := [[]];
	TerminatedEdges := [];

	// Condition to terminate the algorithm
	AllBranchesTerminated := false;

	// Step 1:
	// Initializing graph on level 1
	Level := 1;
	vprint Tretkoff, 1: "Initializing graph-level",Level;
	for j in [1..t] do
		if 1 in RamificationPoints[j][2] then
			e := MakeEdge(<t+1,j>: Level := Level, Branch := [t+1,j]);
			Include(~Vertices,j);
			Append(~EdgesOnLevel[Level],e);
		end if;
	end for;
	
	repeat
		// Step 2: Continuing open branches to sheets
		Level +:= 1;
		vprint Tretkoff, 1: "Constructing graph-level",Level;
		s := 0;
		EdgesOnLevel[Level] := [];
		for Edge in EdgesOnLevel[Level-1] do
			if not Edge`Terminated then
				Perm := RamificationPoints[Edge`EndPt][3];
				l := Edge`StPt - t;
				while Perm ne Id(Sym) do
					k := t + l^Perm;
					if not k in Edge`Branch then
						NewEdge := MakeEdge(<Edge`EndPt,k> : Level := Level, Branch := Append(Edge`Branch,k), Terminated := false);
						s +:= 1;
						NewEdge`Position := s;
						Append(~EdgesOnLevel[Level],NewEdge);
					end if;
					Perm *:= RamificationPoints[Edge`EndPt][3];
				end while;
			end if;
		end for;
		
		// Step 3: Terminate branches at sheets
		vprint Tretkoff, 1: "Terminate branches at graph-level",Level;
		SortedEdgesOnLevel := SortTermEdges(EdgesOnLevel[Level],-1);
		for j in [1..#SortedEdgesOnLevel] do
			Edge := SortedEdgesOnLevel[j];
			if Edge`EndPt in Vertices then
				Edge`Terminated := true;
				Append(~TerminatedEdges,Edge);
			else
				Include(~Vertices,Edge`EndPt);
			end if;
		end for;

		// Step 4:
		// Continuing open branches to ramification points
		Level +:= 1;
		vprint Tretkoff, 1: "Constructing graph-level",Level;
		s := 0;
		EdgesOnLevel[Level] := [];
		for Edge in EdgesOnLevel[Level-1] do
			if not Edge`Terminated then
				l := Edge`EndPt - t;
				k := Edge`StPt mod t + 1;
				for j in [1..t] do
					if l in RamificationPoints[k][2] and not k in Edge`Branch then
						NewEdge := MakeEdge(<Edge`EndPt,k> : Level := Level, Branch := Append(Edge`Branch,k), Terminated := false);
						s +:= 1;
						NewEdge`Position := s;
						Append(~EdgesOnLevel[Level],NewEdge);
					end if;
					k := k mod t + 1;
				end for;
			end if;
		end for;

		// Step 5:
		// Terminate branches at ramification points
		vprint Tretkoff, 1: "Terminate branches at graph-level",Level;
		SortedEdgesOnLevel := SortTermEdges(EdgesOnLevel[Level],1); 
		for j in [1..#SortedEdgesOnLevel] do
			Edge := SortedEdgesOnLevel[j];
			if Edge`EndPt in Vertices then
				Edge`Terminated := true;
				Append(~TerminatedEdges,Edge);
			else
				Include(~Vertices,Edge`EndPt);
			end if;
		end for;

		// Step 6:
		// Check whether all branches are terminated
		AllBranchesTerminated := true;
		for Edge in EdgesOnLevel[Level] do
			if not Edge`Terminated then
				AllBranchesTerminated := false;
				break;
			end if;
		end for;
		vprint Tretkoff, 1: "All branches terminated?",AllBranchesTerminated;
	until AllBranchesTerminated;

	// Cut off empty entries in list
	if #EdgesOnLevel[Level] eq 0 then
		Prune(~EdgesOnLevel);
	end if;

	// Checking correct number of terminated edges
	CTE := 4*g + 2*m - 2;
	CTE2 := Round(CTE/2);
	assert CTE eq #TerminatedEdges;	
	
	vprint Tretkoff,2 : "EdgesOnLevel:",EdgesOnLevel;
	vprint Tretkoff,2 : "#TerminatedEdges:",#TerminatedEdges;
	vprint Tretkoff,2 : "4*Genus + 2*N - 2: ",CTE;

	// Order terminated edges according to RS_SortByBranch
	OrdTermEdges := SortByBranch(EdgesOnLevel,TerminatedEdges);
	
	// Need to go through ordered terminated edges clockwise (instead of counter-clockwise)
	Reverse(~OrdTermEdges);
	vprint Tretkoff,2 : "Ordered terminated edges:",OrdTermEdges;

	// Divide terminated edges into lists P (even level) and Q (odd level) depending on their level
	vprint Tretkoff,1 : "Labeling terminated edges ... ";
	P := []; QQ := []; Q := []; l := 1;
	for k in [1..CTE] do
		Edge := OrdTermEdges[k];
		Edge`Position := [k];
		if Edge`PQ then
			Append(~P,Edge);
			Append(~Edge`Position,l);
			l +:= 1;
		else
			Append(~QQ,Edge);
		end if;
	end for;	
	vprint Tretkoff,2 : "P:", P;
	for k in [1..CTE2] do
		Edge := QQ[k];
		l := Position(P,ReverseEdge(Edge));
		Append(~Edge`Position,l);
		Q[l] := Edge;
	end for;
	vprint Tretkoff,2 : "Q:", Q;
	
	// Piece together the 2g+m-1 cycles
	vprint Tretkoff,1 : "Constructing cycles ... ";
	Cycles := [];
	for j in [1..CTE2] do
		Cycle := P[j]`Branch cat Reverse(Prune(Prune(Q[j]`Branch)));
		k := 1;
		while k le #Cycle-1 do
			Cycle[k] -:= t;
			Cycle[k+1] := RamificationPoints[Cycle[k+1]][1];
			k +:= 2;
		end while;
		Cycle[k] -:= t;
		Append(~Cycles,Cycle);
	end for;
	vprint Tretkoff,2 : "Cycles: ", Cycles;

	// Compute the intersection pairing of the cycles and store them in a matrix K
	vprint Tretkoff,1 : "Computing intersection matrix ... ";
	K := ZeroMatrix(Integers(),CTE2,CTE2);
	for j in [1..CTE2] do
		k := P[j]`Position[1] mod CTE + 1;
		while true do
			NextEdge := OrdTermEdges[k];
			if NextEdge`PQ then
				K[NextEdge`Position[2]][j] +:= 1;
			else
				if NextEdge`Position[2] eq j then
					break;
				else
					K[NextEdge`Position[2]][j] -:= 1;
				end if;
			end if;
			k := k mod CTE + 1;
		end while;
	end for;

	// Checking rank of intersection matrix
	rk := Rank(K); assert rk eq 2*g;
	vprint Tretkoff,2 : "Intersection matrix:",K;
	vprint Tretkoff,2 : "Rank of intersection matrix: ",rk;

	// Return cycles and intersection matrix
	return Cycles, K;
end intrinsic;

/* Routines for symplectic reduction */

procedure MoveToPositivePivot(i,j,pvt,~A,~B)
    	v := A[i][j]; pvtp1 := pvt+1;
	IsPivot := false;
	if [i,j] eq [pvtp1,pvt] and A[pvtp1][pvt] ne v then
		IsPivot := true; SwapRows(~B,pvt,pvtp1); SwapRows(~A,pvt,pvtp1); SwapColumns(~A,pvt,pvtp1);
    	elif [i,j] eq [pvt,pvtp1] then
        	SwapRows(~B,pvt,pvtp1); SwapRows(~A,pvt,pvtp1); SwapColumns(~A,pvt,pvtp1);
    	elif j ne pvt and j ne pvtp1 and i ne pvt and i ne pvtp1 then
        	SwapRows(~B,pvt,j); SwapRows(~B,pvtp1,i); SwapRows(~A,pvt,j); 
		SwapRows(~A,pvtp1,i); SwapColumns(~A,pvt,j); SwapColumns(~A,pvtp1,i);
    	elif j eq pvt then
        	SwapRows(~B,pvtp1,i); SwapRows(~A,pvtp1,i); SwapColumns(~A,pvtp1,i);
   	elif j eq pvtp1 then
        	SwapRows(~B,pvt,i); SwapRows(~A,pvt,i); SwapColumns(~A,pvt,i);
    	elif i eq pvt then
        	SwapRows(~B,pvtp1,j); SwapRows(~A,pvtp1,j); SwapColumns(~A,pvtp1,j);
    	elif i eq pvtp1 then
        	SwapRows(~B,pvt,j); SwapRows(~A,pvt,j); SwapColumns(~A,pvt,j);
	end if;
    	if A[pvtp1][pvt] ne v and not IsPivot then
        	SwapRows(~B,pvt,pvtp1); SwapRows(~A,pvt,pvtp1); SwapColumns(~A,pvt,pvtp1);
	end if;
end procedure;

function SymplecticTransformation(K)
/* Computes a symplectic base change matrix for a skew-symmetric matrix K with entries in {-1,0,1} */

	/* Checking for K to be skew-symmetric */
	assert K + Transpose(K) eq Zero(Parent(K));
	/* Checking for K to be a square matrix */
	n := NumberOfRows(K);
	assert n eq NumberOfColumns(K);
	/* Find the next 1 in L above pvt */
	function FindNextOne(L,pvt)
		for i in [pvt..n] do
			for j in [pvt..n] do
				if L[i][j] eq 1 then
					return [i,j];
				end if;
			end for;
		end for;
		return [0,0];
	end function;

	A := K; // Copy of K
	B := One(Parent(A)); // Identity matrix
    	Inds1 := []; Inds2 := []; // Save indices
    	pvt := 1;
    	while pvt le n do
        	NextOne := FindNextOne(A,pvt);
        	if NextOne eq [0,0] then
            		Append(~Inds2,pvt);
           		pvt +:= 1;
            		continue;
		end if;
       		MoveToPositivePivot(NextOne[2],NextOne[1],pvt,~A,~B);
		ZerosOnly := true;
		pvtp1 := pvt+1;
       		for j in [pvt+2..n] do
			v := -A[pvt][j];
			if v ne 0 then
                		AddRow(~A,v,pvtp1,j); AddColumn(~A,v,pvtp1,j); AddRow(~B,v,pvtp1,j);
				ZerosOnly := false;
			end if;
			v := A[pvtp1][j];
            		if v ne 0 then
				AddRow(~A,v,pvt,j); AddColumn(~A,v,pvt,j); AddRow(~B,v,pvt,j);
				ZerosOnly := false;
			end if;
		end for;
           	if ZerosOnly then
            		Append(~Inds1,[A[pvtp1][pvt],pvt]);
            		pvt +:= 2;
		end if;
	end while;
    	Sort(~Inds1); Reverse(~Inds1);
	NewRowsIndices := [ Ind[2] : Ind in Inds1 ] cat [ Ind[2]+1 : Ind in Inds1 ] cat Inds2;
    	return Matrix([ RowSubmatrix(B,i,1) : i in NewRowsIndices ]);
end function;


intrinsic HomologyBasis(X::RieSrf : Check:=true) -> SeqEnum[SeqEnum[RngIntElt]], Mtrx, Mtrx 
{ Combinatorically computes a symplectic basis of the first homology group of the Riemann surface }
	if not assigned X`HomologyBasis and not X`IsSuperelliptic then
		assert assigned X`LocalMonodromy;
		/* Compute a homology basis and intersection matrix using the Tretkoff algorithm */
		Cycles, K := HomologyBasis(X`LocalMonodromy);
		/* Compute a symplectic base change matrix */
		ST := SymplecticTransformation(K);
		if Check then 
			/* Checking for CF to be in canonical form */
			CF := ST * K * Transpose(ST);
			g := X`Genus; m := X`Degree[1];
			assert IsZero(Submatrix(CF,1,1,g,g)); assert IsZero(Submatrix(CF,g+1,g+1,g,g));
			assert IsZero(Submatrix(CF,1,2*g+1,2*g+m-1,m-1)); assert IsZero(Submatrix(CF,2*g+1,1,m-1,2*g));
			assert IsOne(Submatrix(CF,1,g+1,g,g)); assert IsMinusOne(Submatrix(CF,g+1,1,g,g));
			vprint RS,3 : "Canonical form of intersection matrix:",CF;
			/* Checking unimodularity of symplectic transformation */
			DT := Determinant(ST);
			assert Abs(DT) eq 1;
		end if;
		vprint RS,2 : "Symplectic transformation:",ST; 
		vprint RS,2 : "Determinant of ST:",DT;
		/* Assign homology group */
		X`HomologyBasis := <Cycles, K, ST>;
	end if;
	return X`HomologyBasis[1], X`HomologyBasis[2], X`HomologyBasis[3];
end intrinsic;


/* Intersection matrix & numbers for superelliptic Riemann surfaces */

PI302INV := 1/(2*Pi(RealField(30)));

function SE_IntersectionMatrix(spsm_Matrix, m, n)
	// Building block matrices
	Blocks := [];
	// Block matrix for self-shifts build the diagonal of intersection matrix
	SelfShiftBlock := ZeroMatrix(Integers(),m-1,m-1);
	for Ind1 in [1..m-2] do
		SelfShiftBlock[Ind1][Ind1+1] := 1;
		SelfShiftBlock[Ind1+1][Ind1] := -1;
	end for;
	// Build blocks for intersection matrix
	for j in [1..n-1] do
		Blocks[(j-1)*n+1] := SelfShiftBlock;
		for l in [j+1..n-1] do
			Block := ZeroMatrix(Integers(),m-1,m-1);
			if spsm_Matrix[j][l] ne <0,0> then
				for Ind1 in [1..m-1] do
					sp := spsm_Matrix[j][l][1];
					sm := spsm_Matrix[j][l][2];
					Ind2 := (Ind1 + sp) mod m;
					if Ind2 ne 0 then
						Block[Ind1][Ind2] := 1;
					end if;
					Ind2 := (Ind1 + sm) mod m;
					if Ind2 ne 0 then
						Block[Ind1][Ind2] := -1;
					end if;
				end for;
			end if;
			Blocks[(j-1)*(n-1)+l] := Block;
			Blocks[(l-1)*(n-1)+j] := -Transpose(Block);
		end for;
	end for;
	return BlockMatrix(n-1,n-1,Blocks);
end function;

function SE_IntersectionNumber(Edge1, Edge2, Points, m, n, Zetas)
/* Computes the intersection number between Edge1 and Edge2 */
	mC1 := -One(Universe(Zetas));
	NrOfEndPts := #Set(Edge1`EP cat Edge2`EP);
	// No intersection?
	if NrOfEndPts eq 4 then
		return <0,0>;
	end if;

	// End points
	a := Points[Edge1`EP[1]]; b := Points[Edge1`EP[2]];
	c := Points[Edge2`EP[1]]; d := Points[Edge2`EP[2]];	

	// Excluded trivial cases
	if a eq b or c eq d then
		error Error("Bad edge in spanning tree.");
	end if;
	if ( a eq c and b eq d ) or ( a eq d and d eq c ) then
		error Error("Bad edge in spanning tree.");
	end if;

	/* Arg of factor corresponding to end points */
	phi := Arg(Edge1`Data[n-1]/Edge2`Data[n-1]);

	/* Two cases */
	if a eq c then
		/* Case1: a = c */ 
		AR1 := AC_mthRoot(mC1,Edge1,Zetas,m,n-2);
		AR2 := AC_mthRoot(mC1,Edge2,Zetas,m,n-2);
		Val_ab := Edge1`Data[n+1] * AR2;
		Val_cd := Edge2`Data[n+1] * AR1;
		Val := Val_cd/Val_ab;
		k := Round(PI302INV * (phi + m * Arg(Val)));
		if phi gt 0 then
			return <1-k,-k>;
		else
			return <-k,-1-k>;
		end if;
	elif b eq c then
		/* Case2: b = c */
		AR1 := AC_mthRoot(-mC1,Edge1,Zetas,m,n-2);
		AR2 := AC_mthRoot(mC1,Edge2,Zetas,m,n-2);
		Val_ab := Edge1`Data[n+1] * AR2;
		Val_cd := Edge2`Data[n+1] * AR1;	
		Val := Val_cd/Val_ab;
		k := Round(PI302INV * (phi + m * Arg(Val)) + (1/2));
		return <-k,1-k>;
	else
		error Error("Bad edge in spanning tree.");
	end if;
end function;


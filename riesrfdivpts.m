/*******************************************************************************

	Point class (RieSrfPt) & divisor class (DivRieSrfElt) for Riemann surfaces
 
	Christian Neurohr, Mai 2019

*******************************************************************************/

import "miscellaneous.m": IsWeaklyIn;
import "abeljacobi.m": AJM_DiscriminantPoints;
import "infinitepoints.m": AJM_DE_InfinitePoints;

/* Point class on Riemann surfaces */
declare type RieSrfPt;

declare attributes RieSrfPt: x, y, XYZ, Sheets, RieSrf, IsFinite, Index, IsSingular, RamIndex;

intrinsic Representation(Pt:RieSrfPt) -> .
{ Returns a representation of the RieSrfPt Pt. }
	X := RiemannSurface(Pt);
	C<I> := X`ComplexFields[3];
	if X`IsSuperelliptic then
		if X`IsFinite then
			return ChangeUniverse([Pt`x,Pt`y],C);
		else
			return <Infinity(),Pt`Index>;
		end if;
	else		
		if assigned Pt`y and not Pt`y cmpeq Infinity() then
			return ChangeUniverse([Pt`x,Pt`y],C);
		elif Pt`x cmpeq Infinity() then
			return <Pt`x,Pt`Sheets>;
		elif not assigned Pt`Sheets then
			assert Pt`RamIndex eq 1;
			assert assigned Pt`y;
			Dist, Ind := Distance(Pt`y,X`Fiber(Pt`x));
			assert Dist lt X`WeakError;
			Pt`Sheets := {@ Ind @};
		end if;
		return <C!Pt`x,Pt`Sheets>;
	end if;
end intrinsic;

intrinsic RiemannSurface(Pt::RieSrfPt) -> RieSrf
{ Returns the Riemann surface on which the point Pt is defined. }
	return Pt`RieSrf;
end intrinsic;

intrinsic RamificationIndex(Pt::RieSrfPt) -> RngIntElt
{ Returns the ramification index of the point Pt. }
	if assigned Pt`RamIndex then
		return Pt`RamIndex;
	elif assigned Pt`Sheets then
		return #Pt`Sheets;
	else
		error Error("Not supposed to happen.");
	end if;
end intrinsic;

intrinsic Coordinates(Pt::RieSrfPt) -> SeqEnum[FldComElt]
{ Return the homogeneous coordinates of the point Pt to the precision of its Riemann surface. }
	if not assigned Pt`XYZ then
		assert not Pt`IsFinite;
		X := RiemannSurface(Pt);
		assert not Pt`RieSrf`IsSuperelliptic;
		assert Pt`x cmpeq Infinity();
		if not assigned X`AJM_InfinitePoints then
			AJM_DE_InfinitePoints(X);
		end if;
		C<I> := BaseRing(Parent(X`ComplexDefPol));
		Dist, Ind := Distance(X`AJM_InfinitePoints`Sheets[Pt`Sheets[1]],ChangeUniverse([ P[1] : P in X`InftyCoords ],C));
		if Dist lt X`Error then
			Pt`XYZ := X`InftyCoords[Ind];
		else
			Pt`XYZ := [One(C),0,0];
		end if;
	end if;
	return ChangeUniverse(Pt`XYZ,Pt`RieSrf`ComplexFields[1]);
end intrinsic;
intrinsic IsFinite(Pt::RieSrfPt) -> BoolElt
{ Returns true if Pt is a finite point, false otherwise. }
	return Pt`IsFinite;
end intrinsic;

intrinsic RandomPoint( X::RieSrf : Finite := true, Ht := 10^5 ) -> RieSrfPt
{ Returns a randomly chosen point on the Riemann surface X }
	if Finite then
		C<I> := X`ComplexFields[3];
		x := C!Random([-Ht..Ht])/Random([1..Ht]) + I*C!Random([-Ht..Ht])/Random([1..Ht]);
		S := [x,X`Fiber(x)[Random([1..X`Degree[1]])]];
		yn, Pt := IsCoercible(X,S);
		if yn then
			return Pt;
		else
			return RandomPoint(X:Finite,Ht:=Ht);
		end if;
	else
		return Random(InfinitePoints(X));
	end if;
end intrinsic;

/* Constructor for RieSrfPt */
intrinsic IsCoercible(X::RieSrf,S::Any) -> BoolElt, .
{ Test if S defines a point on the Riemann surface X. }
	f := X`ComplexDefPol;
	C<I> := BaseRing(Parent(f));
	if Type(S) eq SeqEnum then
		if #S eq 1 and X`IsSuperelliptic and S[1] in [1..X`Degree[3]] then
			return true, InfinitePoints(X)[S[1]];
		elif #S eq 2 then
			IsCbl := &and[ IsCoercible(C,s) : s in S ];
			if IsCbl then 
				ChangeUniverse(~S,C);
			else
				return false, "Not a point on the Riemann surface.";
			end if;
			if X`IsSuperelliptic then
				v := Abs(S[2]^X`Degree[1] - Evaluate(f,S[1]));
			else
				v := Abs(Evaluate(f,[S[1],S[2]]));
			end if;
			if v lt X`WeakError then
				if not X`IsSuperelliptic then
					yn, Ind := IsWeaklyIn(S,X`FiniteSingularities,X`WeakError);
					if yn then
                                        	return false, "Singular point of defining polynomial. Not a point on the Riemann surface.";
					end if;
				end if;
				Pt := New(RieSrfPt);
				Pt`x := S[1]; Pt`y := S[2]; Pt`XYZ := [Pt`x,Pt`y,1];
				Pt`RieSrf := X; Pt`IsFinite := true;
				pos := Position(RamificationPoints(X),Pt);
				if pos ne 0 then
					return true, X`RamificationPoints[pos];
				else
					Pt`RamIndex := 1;
					return true, Pt;
				end if;
			else
				return false, "Not a point on the Riemann surface.";
			end if;	
		elif #S eq 3 then
                	IsCbl := &and[ IsCoercible(C,s) : s in S ];
			if IsCbl then 
				ChangeUniverse(~S,C);
			else
				return false, "Not a point on the Riemann surface.";
			end if;
			if S[3] ne 0 then
				return IsCoercible(X,[S[1]/S[3],S[2]/S[3]]);
			else
				Pt := New(RieSrfPt); Pt`RieSrf := X; Pt`IsFinite := false;
				Pt`XYZ := ChangeUniverse(S,C);
				yn, Ind := IsWeaklyIn(Pt`XYZ,X`SingularPoints,X`WeakError);
				if yn then
                                        return false, "Singular point of the projective closure. Not a point on the Riemann surface.";
				end if;
				yn, Ind := IsWeaklyIn(Pt`XYZ,[ Coordinates(InfPt) : InfPt in InfinitePoints(X) ],X`WeakError);
				if yn then
					return true, InfinitePoints(X)[Ind];
				else
				        return false, "Not on a point the Riemann surface.";
				end if;
			end if;
		end if;
	elif Type(S) eq Tup and not X`IsSuperelliptic then
		if S[2] in [1..X`Degree[1]] then
			if S[1] cmpeq Infinity() then
				for Pt in X`InfinitePoints do
					if S[2] in Pt`Sheets then
						return true, Pt;
					end if;
				end for;
			else
				x := C!S[1];
				Dist, Ind := Distance(x,X`DiscriminantPoints);
				if Dist gt X`Error then
					return IsCoercible(X,[x,X`Fiber(x)[S[2]]]);
				else
					for Pt in X`ClosedChains[Ind]`Points do
						if S[2] in Pt`Sheets then
							return true, Pt;
						end if;
					end for;
				end if;
			end if;
		end if;
	end if;
        return false, "Not a point on the Riemann surface";
end intrinsic;

intrinsic Point(X::RieSrf,S::SeqEnum) -> RieSrfPt
{ Creates a point on the Riemann surface X with coordinates S. }
	return IsCoercible(X,S);
end intrinsic;

intrinsic Point(X::RieSrf,S::Tup) -> RieSrfPt
{ Creates a point on the Riemann surface from a tuple S = <x,s> where x is a complex number or Infinity() and s is a sheet number on the Riemann surface X. }
	return IsCoercible(X,S);
end intrinsic;

intrinsic Print(Pt::RieSrfPt:Precision:=10)
{ Printing for type RieSrfPt. }
	C<I> := ComplexField(Precision);
	if Pt`IsFinite then
		if assigned Pt`y and Type(Pt`y) eq FldComElt then
			printf "(" cat Sprint(C!Pt`x) cat ", " cat Sprint(C!Pt`y) cat ")";
		else
			printf "(" cat Sprint(C!Pt`x) cat ", " cat Sprint(Pt`Sheets) cat ")";
		end if;
	else
		if Pt`RieSrf`IsSuperelliptic then
			if Pt`Index eq 1 then
				printf "1st point at infinity";
			elif Pt`Index eq 2 then
				printf "2nd point at infinity";
			elif Pt`Index eq 3 then
				printf "3rd point at infinity";
			else
				printf Sprint(Pt`Index) cat "th point at infinity";
			end if;
		else
			if Pt`x cmpeq Infinity() and assigned Pt`Sheets then
				printf "Point at infinity on sheets " cat Sprint(Pt`Sheets);
			elif Type(Pt`x) eq FldComElt and not assigned Pt`y then
				printf "Point over x = " cat Sprint(C!Pt`x) cat " on sheets " cat Sprint(Pt`Sheets);
			elif Type(Pt`x) eq FldComElt and Pt`y cmpeq Infinity() then
				printf "Y-infinite point over x = " cat Sprint(C!Pt`x) cat " on sheets " cat Sprint(Pt`Sheets);
			else
				error Error("Error in print.");
			end if;
		end if;
	end if;
end intrinsic;

intrinsic 'eq'(P::RieSrfPt,Q::RieSrfPt) -> BoolElt
{ Checks whether two RieSrfPt objects are equal. }
	X := P`RieSrf;
	if X ne Q`RieSrf then
		return false;
	end if; 
	if P`IsFinite and Q`IsFinite then
		if Abs(P`x-Q`x) gt X`WeakError then
			return false;
		else
			if assigned P`y and assigned Q`y then
				return  Abs(P`y-Q`y) lt X`WeakError;
			elif assigned P`Sheets and assigned Q`Sheets then
				return Set(P`Sheets) eq Set(Q`Sheets);
			else
				return false;
			end if;
		end if;
	end if;
	if not P`IsFinite and not Q`IsFinite then
		if X`IsSuperelliptic then
			if assigned P`Index and assigned Q`Index then
				return P`Index eq Q`Index;
			elif assigned P`XYZ and assigned Q`XYZ then
				assert P`XYZ[3] eq 0; assert Q`XYZ[3] eq 0;
				if P`XYZ[1] ne 0 then
					if Q`XYZ[1] ne 0 then
						return Abs(P`XYZ[2]/P`XYZ[1]-Q`XYZ[2]/Q`XYZ[1]) lt X`WeakError;
					else
						return false;
					end if;
				else
					return Q`XYZ[1] eq 0;
				end if;
			end if;
		else
			if assigned P`x and assigned Q`x then
				if P`x cmpeq Infinity() and Q`x cmpeq Infinity() then
					return Set(P`Sheets) eq Set(Q`Sheets);
				elif Type(P`x) eq FldComElt and Type(Q`x) eq FldComElt and Abs(P`x - Q`x) lt X`WeakError then
					return Set(P`Sheets) eq Set(Q`Sheets);
				end if;
			elif assigned P`XYZ and assigned Q`XYZ then
				assert P`XYZ[3] eq 0; assert Q`XYZ[3] eq 0;
				if P`XYZ[1] ne 0 then
					if Q`XYZ[1] ne 0 then
						return Abs(P`XYZ[2]/P`XYZ[1]-Q`XYZ[2]/Q`XYZ[1]) lt X`WeakError;
					else
						return false;
					end if;
				else
					return Q`XYZ[1] eq 0;
				end if;
			end if;
		end if;
	end if;
	return false;
end intrinsic;

procedure AnalyzeSpecialPoints(X)
/* Determine singular points and other special points on the Riemann surface */
	if not assigned X`InfinitePoints or not assigned X`YInfinitePoints or not assigned X`SingularPoints then
	X`InfinitePoints := [];
	X`YInfinitePoints := [];
	X`SingularPoints := [];
	m := X`Degree[1];
	if X`IsSuperelliptic then
		C<I> := X`ComplexFields[3];
		n := X`Degree[2]; 
		d := X`Degree[3];
		if m eq n then
			LCm := Exp((1/m)*Log(X`LeadingCoeff));
			for k in [1..m] do
				PtAtInf := New(RieSrfPt); PtAtInf`RieSrf := X;
				PtAtInf`x := Infinity(); PtAtInf`y := Infinity();
				PtAtInf`XYZ := [ 1/(X`Zetas[2*k-1] * LCm), 1 , 0 ];
				PtAtInf`IsFinite := false; PtAtInf`RamIndex := 1;  PtAtInf`Index := k;
				Append(~X`InfinitePoints,PtAtInf);
			end for;
		elif m gt n then
			if m ne n+1 then
				Append(~X`SingularPoints,[1,0,0]);
			end if;	
			for k in [1..d] do
				PtAtInf := New(RieSrfPt); PtAtInf`RieSrf := X; PtAtInf`Index := k; PtAtInf`RamIndex := m/d;
				PtAtInf`x := Infinity(); PtAtInf`y := Infinity(); PtAtInf`XYZ := [1,0,0];
				PtAtInf`IsFinite := false; Append(~X`InfinitePoints,PtAtInf);
			end for;
		elif m lt n then
			if m ne n-1 then
				Append(~X`SingularPoints,[0,1,0]);
			end if;
			for k in [1..d] do
				PtAtInf := New(RieSrfPt); PtAtInf`RieSrf := X; PtAtInf`Index := k; PtAtInf`RamIndex := m/d;
				PtAtInf`x := Infinity(); PtAtInf`y := Infinity(); PtAtInf`XYZ := [0,1,0];
				PtAtInf`IsFinite := false; Append(~X`InfinitePoints,PtAtInf);
			end for;
		end if;
	else
		C<I> := BaseRing(Parent(X`ComplexDefPol));
		Cz<z> := PolynomialRing(C);
		dfx := Derivative(X`ComplexDefPol,1);
		dfy := Derivative(X`ComplexDefPol,2);
		X`CriticalValues := [];
		X`CriticalPoints := [];
		X`FiniteSingularities := {};
		X`YInfinitePoints := [];
		/* Finite points as centers of closed chains */
		for k in [1..#X`ClosedChains] do
			Ch := X`ClosedChains[k];
			Ch`Points := [];
			xk := Ch`Center;
			Yk := X`Fiber(xk);
			dfxk := Evaluate(dfx,[xk,z]);
			dfyk := Evaluate(dfy,[xk,z]);
			ChPerm := Ch`Permutation;
			CD := CycleDecomposition(ChPerm);
			/* Infinite points in the fiber? */
			if #Yk eq 0 then
				for k in [1..#CD] do
					Pt := New(RieSrfPt); Pt`RieSrf := X; Pt`x := xk;
					Pt`Index := k;
					Pt`Sheets := CD[k];
					Pt`IsFinite := false;
					Pt`y := Infinity(); Pt`XYZ := [0,1,0];
					Append(~X`YInfinitePoints,Pt);
					Append(~Ch`Points,Pt);
				end for;
			elif #Yk lt m then
				/* These points cannot be identified (in our setting) without integrating into the center, may take some time */
				if not IsDefined(X`AJM_DiscriminantPoints,k) then
					AJM_DiscriminantPoints(X,k);
				end if;
				for l in [1..#CD] do
					Pt := New(RieSrfPt); Pt`RieSrf := X; Pt`x := xk;
					Pt`Index := l;
					Pt`Sheets := CD[l]; Pt`RamIndex := #Pt`Sheets;
					Dist, Ind := Distance(X`AJM_DiscriminantPoints[k]`Sheets[Pt`Sheets[1]],Yk);
					if Dist gt X`WeakError then
						Pt`IsFinite := false;
						Pt`y := Infinity(); Pt`XYZ := [0,1,0];
						Append(~X`YInfinitePoints,Pt);
					else
						Pt`IsFinite := true;
						Pt`y := Yk[Ind]; Pt`XYZ := [Pt`x,Pt`y,1];
						Val1 := Abs(Evaluate(dfxk,Pt`y));
						Val2 := Abs(Evaluate(dfyk,Pt`y));
						if Val2 lt X`WeakError then
							if Val1 lt X`WeakError then
								Include(~X`FiniteSingularities,[Pt`x,Pt`y]);
								delete Pt`y;
							end if;
							Append(~X`CriticalValues,xk);
							Append(~X`CriticalPoints,Pt);
						end if;
					end if;
					Append(~Ch`Points,Pt);
				end for;
				assert #Ch`Points eq #CD;	
			else
				for l in [1..#CD] do
					Pt := New(RieSrfPt);
					Pt`RieSrf := X; Pt`IsFinite := true;
					Pt`Index := l; Pt`Sheets := CD[l]; Pt`RamIndex := #Pt`Sheets;
					Pt`x := xk; Pt`y := Yk[Pt`Sheets[1]];
					Pt`XYZ := [Pt`x,Pt`y,1];
					Val1 := Abs(Evaluate(dfxk,Pt`y));
					Val2 := Abs(Evaluate(dfyk,Pt`y));
					if Val2 lt X`WeakError then
						if Val1 lt X`WeakError then
							Include(~X`FiniteSingularities,[Pt`x,Pt`y]);
							delete Pt`y;
						end if;
						Append(~X`CriticalValues,xk);
						Append(~X`CriticalPoints,Pt);
					end if;
					Append(~Ch`Points,Pt);
				end for;
				assert #Ch`Points eq #CD;
			end if;
		end for;
		X`FiniteSingularities := SetToSequence(X`FiniteSingularities);

		/* Analyze points at infinity */
		FXYZ0 := &+[ T : T in Terms(X`ComplexDefPol) | Degree(T) eq Degree(X`ComplexDefPol) ];
		SFX1 := Roots(Evaluate(FXYZ0,[1,z])); SFX1 := [ r[1] : r in SFX1 ];
		SFY1 := Roots(Evaluate(FXYZ0,[z,1])); SFY1 := [ r[1] : r in SFY1 ];
		AllPoints := { };
		for y in SFX1 do
			if Abs(y) lt X`Error then
				Pt := [One(C),0,0];
			else
				Pt := [1/y,1,0];
			end if;
			Include(~AllPoints,Pt);
		end for;
		for k in [1..#SFY1] do
			xk := SFY1[k]; 
			if Abs(xk) lt X`Error then
				Pt := [0,One(C),0];
			else
				if Distance(xk,[ P[1] : P in AllPoints]) gt X`Error then
					Pt := [xk,1,0];
				end if;
			end if;
			Include(~AllPoints,Pt);
		end for;
		X`InftyCoords := SetToSequence(AllPoints);
		DF := [ Derivative(X`ComplexHomoDefPol,k) : k in [1,2,3] ];
		X`InfiniteSingularities := [];
		for k in [1..#X`InftyCoords] do
			Pt := X`InftyCoords[k];
			DFP := [ Evaluate(DFK,Pt) : DFK in DF ];
			if &and[ Abs(v) lt X`Error : v in DFP ] then
				vprint RS,2 : "Singular infinite point:",Pt;
				Append(~X`InfiniteSingularities,Pt);
			end if;
		end for;
		X`SingularPoints := [ Append(P,1) : P in X`FiniteSingularities ] cat X`InfiniteSingularities;
		X`InfiniteChain`Points := [];
		InfPerm := X`InfiniteChain`Permutation;
		CD := CycleDecomposition(InfPerm);
		for k in [1..#CD] do
			Pt := New(RieSrfPt); Pt`x := Infinity(); Pt`y := Infinity();
			Pt`RieSrf := X; Pt`IsFinite := false;
			Pt`Index := k; Pt`Sheets := CD[k]; Pt`RamIndex := #Pt`Sheets;
			Append(~X`InfiniteChain`Points,Pt);
		end for;
		X`InfinitePoints := X`InfiniteChain`Points;
	end if;
	vprint RS,2 : "X`SingularPoints:",X`SingularPoints;
	end if;
end procedure;

intrinsic PointsOverDiscriminantPoint(X::RieSrf,k::RngIntElt) -> SeqEnum[RieSrfPt]
{ Returns the sequence of RieSrfPt lying over the k-th discriminant points of X. If k is zero, return the points lying above infinity. }
	require k in [0..#X`DiscriminantPoints] : "There are only",#X`DiscriminantPoints,"discriminant points.";
	if not assigned X`SingularPoints then
		AnalyzeSpecialPoints(X);
	end if;
	if k eq 0 then
		if X`IsSuperelliptic then
			return X`InfinitePoints;
		else
			return X`InfiniteChain`Points;
		end if;
	else
		if X`IsSuperelliptic then
			return X`CriticalPoints[k];
		else
			return X`ClosedChains[k]`Points;
		end if;
	end if;
end intrinsic;

/* Divisor-class on Riemann surfaces */
declare type DivRieSrfElt;

declare attributes DivRieSrfElt: RieSrf, Points, Mults, Degree, AJM, Place, FFDiv;

/* Construction of DivRieSrfElt */
intrinsic Divisor(S::SeqEnum[RieSrfPt],V::SeqEnum[RngIntElt]) -> DivRieSrfElt
{ The divisor on the RieSrfPt's in S and multiplicities in V. }
	D := New(DivRieSrfElt);
	nS := #S; 
	assert nS eq #V;
	assert nS gt 0;
	D`RieSrf := RiemannSurface(S[1]);
	D`Degree := &+V;
	D`Points := []; D`Mults := [];
	for k in [1..nS] do
		if V[k] ne 0 then
			Append(~D`Points,S[k]);
			Append(~D`Mults,V[k]);
		end if;
	end for;
	return D;
end intrinsic;
intrinsic ZeroDivisor(X::RieSrf) -> DivRieSrfElt
{ The zero divisor on the Riemann surface X. }
	D := New(DivRieSrfElt);
	D`RieSrf := X;
	D`Degree := 0;
	D`Points := []; 
	D`Mults := [];
	return D;
end intrinsic;
intrinsic RiemannSurface(D::DivRieSrfElt) -> RieSrf
{ Returns the Riemann surface on which the divisor is defined. }
	return D`RieSrf;
end intrinsic;
intrinsic Support(D::DivRieSrfElt) -> SeqEnum[RieSrfPt], SeqEnum[RngIntElt]
{ Returns the support and the multiplicties of the divisor D. }
	return D`Points, D`Mults;
end intrinsic;
intrinsic Degree(D::DivRieSrfElt) -> RngIntElt
{ Returns the degree of the divisors D. }
	return D`Degree;
end intrinsic;
intrinsic 'eq'(D1::DivRieSrfElt,D2::DivRieSrfElt) -> BoolElt
{ Equality on DivRieSrfElt. }
	Points1, Mults1 := Support(D1);
	Points2, Mults2 := Support(D2);
	return ( Points1 eq Points2 ) and ( Mults1 eq Mults2 );
end intrinsic;
intrinsic '+'(P1::RieSrfPt,P2::RieSrfPt) -> DivRieSrfElt
{ Add points on X. }
	return Divisor([P1,P2],[1,1]);
end intrinsic;
intrinsic '-'(P1::RieSrfPt,P2::RieSrfPt) -> DivRieSrfElt
{ Subtract points on X. }
	return Divisor([P1,P2],[1,-1]);
end intrinsic;
intrinsic '+'(D::DivRieSrfElt,P::RieSrfPt) -> DivRieSrfElt
{ Add a point to a divisor. }
	return D + 1*P;
end intrinsic;
intrinsic '-'(D::DivRieSrfElt,P::RieSrfPt) -> DivRieSrfElt
{ Subtract a point from a divisor. }
	return D - 1*P;
end intrinsic;
intrinsic '+'(D1::DivRieSrfElt,D2::DivRieSrfElt) -> DivRieSrfElt
{ Add two divisors on X. }
	require D1`RieSrf eq D2`RieSrf : "Divisors have to be defined on the same Riemann surface.";
	Points1, Mults1 := Support(D1);
	Points2, Mults2 := Support(D2);
	for k in [1..#Points2] do
		P := Points2[k];
		Ind := Position(Points1,P);
		if Ind eq 0 then
			Append(~Points1,P);
			Append(~Mults1,Mults2[k]);
		else
			Mults1[Ind] +:= Mults2[k];
		end if;
	end for;
	D := Divisor(Points1,Mults1);
	if assigned D1`AJM and assigned D2`AJM then
		D`AJM := D1`AJM + D2`AJM;
	end if;
	return D;
end intrinsic;
intrinsic '-'(D1::DivRieSrfElt,D2::DivRieSrfElt) -> DivRieSrfElt
{ Subtract divisors. }
	return D1 + (-1)*D2;
end intrinsic;
intrinsic '*'(k::RngIntElt,P::RieSrfPt) -> DivRieSrfElt
{ Multiplication of points on X. }
	return Divisor([P],[k]);
end intrinsic;
intrinsic '*'(k::RngIntElt,D::DivRieSrfElt) -> DivRieSrfElt
{ Multiplication of divisors on X. }
	if k eq 0 then
		return ZeroDivisor(RiemannSurface(D));
	end if;
	Points, Mults := Support(D);
	kD := Divisor(Points,[k*Mults[l] : l in [1..#Points]]);
	if assigned D`AJM then
		kD`AJM := k * D`AJM;
	end if;
	return kD;
end intrinsic;
intrinsic Print( D::DivRieSrfElt : Precision := 10 )
{ Printing for divisors on Riemann surfaces }
	C<I> := ComplexField(Precision);
	X := RiemannSurface(D);
	Points, Mults := Support(D);
	S := "";
	for k in [1..#Points] do
		Pt := Points[k]; vP := Mults[k];
		if Sign(vP) eq 1 then
			if k gt 1 then
				S cat:= " + ";
			end if;
		else
			if k gt 1 then
				S cat:= " - ";
			else
				S cat:= "-";
			end if;
		end if;
		AvP := Abs(vP);
		if AvP ne 1 then
			S cat:= Sprint(AvP) cat "*";
		end if;
		if Pt`IsFinite then
			if assigned(Pt`y) and Type(Pt`y) eq FldComElt then
				S cat:= "(" cat Sprint(C!Pt`x) cat "," cat Sprint(C!Pt`y) cat ")";
			else
				S cat:= "(" cat Sprint(C!Pt`x) cat "," cat "s" cat Sprint(Pt`Sheets) cat ")";
			end if;
		else
			if X`IsSuperelliptic then
				S cat:= "(Infty,#" cat Sprint(Pt`Index) cat ")";
			else
				if Pt`x cmpeq Infinity() then
					S cat:=  "(" cat Sprint(Pt`x) cat "," cat "s" cat Sprint(Pt`Sheets) cat ")";
				elif Type(Pt`x) eq FldComElt then
					S cat:=  "(" cat Sprint(C!Pt`x) cat "," cat "s" cat Sprint(Pt`Sheets) cat ")";
				else
					error Error("Not supposed to happen.");
				end if;
			end if;
		end if;
	end for;
	print S;
	if assigned D`Place then
		print "Place:",D`Place,"of degree",Degree(D`Place);
	end if;
	if assigned D`FFDiv then
		print "Function field divisor:",D`FFDiv;
	end if;
	if assigned D`AJM then
		print "Abel-Jacobi:",assigned D`AJM;
	end if;
end intrinsic;
intrinsic RandomDivisor( X::RieSrf, d::RngIntElt : Ht := 10^5, Zero := false ) -> DivRieSrfElt
{ Creates a random divisor on the Riemann surface X. }
	Points := []; Mults := [];
	for k in [1..d] do
		Append(~Points,RandomPoint(X:Ht:=Ht));
		Append(~Mults,Random([-1,1])*Random([1..Ht]));
	end for;
	if Zero then
		Deg := &+Mults;
		Mults[1] -:= Deg;
	end if;
	return Divisor(Points,Mults);
end intrinsic;

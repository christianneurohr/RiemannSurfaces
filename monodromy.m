/*******************************************************************************

	Monodromy representation & analytic continuation for Riemann surfaces
 
	Christian Neurohr, June 2019

*******************************************************************************/

import "paths.m": ReversePath;
import "miscellaneous.m": EmbedPolynomial, ModifiedFiber, CompareFldComElt;


procedure AnalyticContinuation( f, Gamma )
/* Assign the permutation induced by f to Gamma */
	if not assigned Gamma`Permutation then
	CC<I> := Parent(Gamma`StartPt);
	Cz<z> := PolynomialRing(CC);
	OH := One(CC)/2;
	RL := RealField(3);
	
	/* Heuristically estimate number of steps */
	st := Ceiling(Gamma`Length) + 1;	
	if Gamma`Type in ["Arc", "FullCircle"] then
		st *:= 4;
	end if;
	Steps := [ l/st : l in [-st+1..st-1] ];
	vprint RS, 1 : "Estimated number of steps to analytically continue path:",#Steps;
	
	vprint RS,1 : "Performing analytic continuation...";
	vprint RS,2 : "along:",Gamma;
	vprint RS,2 : "of length:",Gamma`Length;
	vprint RS,1 : "using steps:",#Steps;
	vprint RS,3 : "Starting Interval:",Steps;

	/* Analytic continuation */
	m := Degree(f,2);
	RMV := [ Remove([1..m],j) : j in [1..m] ];
	Err := 10^(-Precision(CC)+20);
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
	function ACRecursion(p,x1,x2,Z)
		px2 := Evaluate(p,[x2,z]);
		px2 *:= 1/LeadingCoefficient(px2);
		W := [ Evaluate(px2,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
		w0 := Max( [ (RL!Re(W[j]))^2+(RL!Im(W[j]))^2 : j in [1..m] ]);
		if w0 lt Err2 then
			return Z;
		end if;
		if 16*w0 lt DistSquared(Z) then
			repeat
				Z := [ Z[j] - W[j] : j in [1..m] ];
				W := [ Evaluate(px2,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
				w0 := Max([ (RL!Re(W[j]))^2+(RL!Im(W[j]))^2 : j in [1..m] ]);
			until w0 lt Err2;
			return Z;
		else
			x1x2 := (x1+x2)*OH;
			return ACRecursion(p,x1x2,x2,ACRecursion(p,x1,x1x2,Z));
		end if;	
	end function;
	
	/* Run through steps */
	xj := Gamma`Evaluate(Steps[1]);
	yj := ACRecursion(f,Gamma`StartPt,xj,ModifiedFiber(f,Gamma`StartPt));
	for j in [2..#Steps-1] do
		nxj := Gamma`Evaluate(Steps[j+1]);
		yj := ACRecursion(f,xj,nxj,yj);
		xj := nxj;
	end for;
	yj := ACRecursion(f,xj,Gamma`EndPt,yj);
	Ok, Sigma := Sort(yj,CompareFldComElt);
	Gamma`Permutation := Inverse(Sigma);
	end if;
end procedure;

procedure ChainPermutation(f, Ch)
/* Computes the permutation of the chain Ch */
	for p in Ch`Paths do
		if not assigned p`Permutation then
			AnalyticContinuation(f,p);
		end if;
	end for;
	Ch`Permutation := &*[ p`Permutation : p in Ch`Paths ];
end procedure;

intrinsic MonodromyRepresentation(f::RngMPolElt:BasePoint:="Clever" ) -> SeqEnum[CChain]
{ Computes the local monodromy of the branched covering associated to f(x,y)=0 w.r.t. projecting on the x-plane. }
	Kxy := Parent(f);
	K := BaseRing(Kxy);
	require K eq Rationals() : "Polynomial has to be defined over the rationals.";
	K := RationalsAsNumberField();
	f := ChangeRing(f,K);
	P := InfinitePlaces(K)[1];
	return MonodromyRepresentation(f,P:BasePoint:=BasePoint);
end intrinsic;
intrinsic MonodromyRepresentation(f::RngMPolElt,P::PlcNumElt: BasePoint:="Clever" ) -> SeqEnum[CChain]
{ Computes the local monodromy of the branched covering associated to f(x,y)=0 w.r.t. projecting on the x-plane. }

	/* Polynomial ring */
	Kxy<x,y> := Parent(f);
	K := BaseRing(Kxy);
	vprint RS,1 : "Defining polynomial:",f;
	require Type(K) eq FldNum : "Polynomial has to be defined over a number field.";
	require IsInfinite(P) : "PlcNumElt has to be infinite";

	/* Discriminant Points */
	DP, XYB, BYValues := DiscriminantPoints(f,P);	

	/* Embed polynomial */
	C<I> := Universe(DP);
	Cxy<x,y> := PolynomialRing(C,2);
	f := EmbedPolynomial(f,P,Cxy);
	vprint RS,2 : "Precision:",Precision(C);

	/* Symmetric group on N elements (sheets) */
	m := Degree(f,2);
	Sym := Sym(m);
	Id := Id(Sym);
	vprint RS,2 : "#Sheets:",m;

	/* Compute fundamental group */
	vprint RS,2 : "BasePoint:",BasePoint;
	BP, ODP, PathPieces, IndexPathLists, SafeRadii := FundamentalGroup(DP : BasePoint := BasePoint);
	vprint RS,2 : "BasePoint:",BP;
	vprint RS,2 : "Ordered discriminant points:",ChangeUniverse(ODP,ComplexField(10));

	/* Construct chains from path pieces */
	ClosedChains := [];
	vprint RS,1 : "Constructing chains and analytic continuation...";
	assert #IndexPathLists eq #ODP;
	for l in [1..#IndexPathLists] do
		IndexList := IndexPathLists[l];
		NextPath := [];
		for Index in IndexList do
			if Sign(Index) eq 1 then
				Append(~NextPath,PathPieces[Index]);
			else
				Append(~NextPath,ReversePath(PathPieces[-Index]));
			end if;
		end for;
		NextChain := Chain(NextPath:Center:=ODP[l]);
		vprint RS,2 : "Continuing chain nr.",l;
		ChainPermutation(f,NextChain);
		if NextChain`Permutation ne Id then
			Append(~ClosedChains,NextChain);
		end if;
	end for;

	vprint RS,1 : "Checking point at infinity...";
	/* Compute permutation at infinity by relation */
	LocalMonodromy := [ Ch`Permutation : Ch in ClosedChains ];
	if #LocalMonodromy gt 0 then
		InfPerm := Inverse(&*LocalMonodromy);
		vprint RS,2 : "Permutation at infinity:",InfPerm;
		/* Chain around infinity */
		if InfPerm ne Id then
			InfChain := (&*[ Ch : Ch in ClosedChains ])^-1;
			InfChain`Center := Infinity();
			Append(~ClosedChains,InfChain);
			Append(~LocalMonodromy,InfPerm);
		end if;
	end if;
	return ClosedChains;
end intrinsic;

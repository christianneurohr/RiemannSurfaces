/*******************************************************************************

	Complex paths and chains (for integration of differentials)
 
	Christian Neurohr, September 2018

*******************************************************************************/

import "monodromy.m": AnalyticContinuation;

declare type CPath;
declare attributes CPath: StartPt, EndPt, Type, Radius, Center, Length, Orientation, Permutation, IntPar, Integrals, StartArg, EndArg, Bounds, Evaluate, Subpaths, WP, IN, N, Sheets, IntMethod, Error;

function ModifiedArg(z:Rotate:=0)
/* Given a complex number z, return the argument (in [0 and 2Pi]) of z translated by -Rotate */
	Argument := Arg(z);
	if Rotate ne 0 then
		Argument -:= Rotate;		
	end if;
	while Argument lt 0 do
		Argument +:= 2*Real(Pi(Parent(z)));
	end while;
	return Argument;
end function;

/* Constructor */
function Path( StartPt, EndPt, Type : Radius := 0, Center := 0, Orientation := 1, Bounds := [] )
	assert Orientation in [-1,1];
	assert Type in ["LineSegment","FullCircle","Arc","Point","InfiniteLine"];
	assert Radius ge 0;
	CC := Parent(StartPt);
	assert Parent(EndPt) eq CC;
	PI_CC := Real(Pi(CC));
	p := New(CPath);
	p`StartPt := StartPt;
	p`EndPt := EndPt;
	p`Type := Type;
	p`Bounds := Bounds;
	if p`Type ne "LineSegment" then
		p`Radius := Radius;
		p`Center := Center;
		p`Orientation := Orientation;
		if p`Type eq "Arc" then
			StartArg := ModifiedArg(StartPt-Center);
			EndArg := ModifiedArg(EndPt-Center);
			if Orientation eq 1 and EndArg lt StartArg then
				EndArg +:= 2*PI_CC;
			elif Orientation eq -1 and StartArg lt EndArg then
				StartArg +:= 2*PI_CC;
			end if;
			p`StartArg := StartArg;
			p`EndArg := EndArg;
		elif p`Type eq "FullCircle" then
			p`StartArg := ModifiedArg(p`StartPt - p`Center);
			p`EndArg := p`StartArg;
		end if;
	end if;

	/* Assign evaluate function & length */
	if p`Type eq "LineSegment" then
		dx_t := (p`EndPt-p`StartPt)/2;
		p`Length := 2 * Abs(dx_t);
		xt := dx_t + p`StartPt;
		function G(t)
			return  xt + dx_t * t, dx_t;
		end function;
	elif p`Type eq "Point" then
		p`Length := 0;
		function G(t)
			return p`StartPt, 0;
		end function;
	elif p`Type eq "InfiniteLine" then
		p`EndPt := Infinity();
		p`Length := Infinity();
		function G(t)
			c1 := 1/(1-t);
			c2 := 2 * p`StartPt * c1;
			return c2, c2*c1;
		end function;
	else
		if p`Type eq "FullCircle" then
			c1 := (-1) * p`Radius * Exp(CC.1 * p`StartArg);
			c2 := PI_CC * CC.1 * p`Orientation;
			p`Length := 2 * PI_CC * p`Radius;
		elif p`Type eq "Arc" then
			c1 := p`Radius * Exp(CC.1*(p`EndArg + p`StartArg)/2);
			c2 := CC.1*(p`EndArg - p`StartArg)/2;
			Angle := p`Orientation * (ModifiedArg(p`EndPt - p`Center) - ModifiedArg(p`StartPt - p`Center));
			if Angle lt 0 then
				Angle +:= 2*PI_CC;
			end if;
			p`Length := Angle * p`Radius;
			assert p`Length gt 0;
		end if;
		function G(t)
			xt := c1 * Exp(c2*t);
			return  xt + p`Center, c2 * xt;
		end function;
	end if;
	p`Evaluate := G;
	return p;   
end function;

intrinsic Print( p::CPath : Precision := 10 )
{ Print Path }
	C<I> := ComplexField(Precision);
	if p`Type eq "LineSegment" then
    		print "LineSegment from",C!p`StartPt,"to",C!p`EndPt;
	elif p`Type eq "Arc" then
		print "Arc around", C!p`Center, "with Radius",C!p`Radius,"and Orientation",p`Orientation,"from",C!p`StartPt,"to",C!p`EndPt;
	elif p`Type eq "FullCircle" then
    		print "FullCircle around",C!p`Center,"with Radius",C!p`Radius,"and Orientation",p`Orientation,"starting at",C!p`StartPt;
	elif p`Type eq "Point" then
    		print "Point at",C!p`StartPt;
	elif p`Type eq "InfiniteLine" then
		print "Line to infinity starting at",C!p`StartPt;
	else
		print "Error: Unknown type",p`Type;
	end if;
	if assigned p`Permutation then
		print "and permutation:",p`Permutation;
	end if;
end intrinsic;
function CPoint( x )
/* Create the point x in the complex plane as a CPath object */
	return Path(x,x,"Point" : Radius:=0, Center:=x );
end function;
function CLineSegment( x, y )
/* Creates a straight line from x to y */
	return Path(x,y,"LineSegment");
end function;
function CFullCircle( x, c : o := 1 )
/* Create a full circle starting at x around c and orientation O */
	return Path(x,x,"FullCircle": Radius := Abs(x-c), Center := c, Orientation := o );
end function;
function CArc( x, y, c : o := 1 )
/* Creates an arc from x to y around c with orientation o } */
	if Abs(x-y) lt 10^-Precision(x) then
		return CFullCircle(x, c : o := o );
	else
		return Path(x,y,"Arc" : Radius := Abs(x-c), Center := c, Orientation := o );			
	end if;
end function;
function CInfiniteLine( x )
/* Create a path from 0 \ne x to \infty in the direction of x */
	assert x ne 0;
	return Path(x,x,"InfiniteLine");
end function;

/* Define equality for type CPath */
intrinsic 'eq'( p::CPath, q::CPath ) -> BoolElt
{ Returns true if c = d, false otherwise }
	if p`Type ne q`Type then
		return false;
	end if;
	if p`Type eq "LineSegment" then
		return (p`StartPt eq q`StartPt) and (p`EndPt eq q`EndPt);
	elif p`Type eq "Arc" then
		return (p`StartPt eq q`StartPt) and (p`EndPt eq q`EndPt) and (p`Center eq q`Center) and (p`Orientation eq q`Orientation) or
		(p`StartPt eq q`EndPt) and (p`EndPt eq q`StartPt) and (p`Center eq q`Center) and (p`Orientation eq (-1)*q`Orientation);
	elif p`Type eq "FullCircle" then
		return (p`Center eq q`Center) and (p`Radius eq q`Radius) and (p`Orientation eq q`Orientation);
	elif p`Type in ["InfiniteLine","Point"] then
		return p`StartPt eq q`StartPt;
	end if;
end intrinsic;

function PermuteVector( V,Sigma,m )
/* Permute the entries of the (mx1)-vector V by Sigma */
	return Matrix(BaseRing(V),m,1,[ V[j^Sigma][1] : j in [1..m]]);
end function;
function PermuteMatrix( M,Sigma,m,g )
/* Permute the rows of the (mxg)-matrix M by Sigma */
	return Matrix(BaseRing(M),m,g,[ M[j^Sigma] : j in [1..m]]);
end function;

function ReversePath( p )
/* For a given path p, returns a sequence of inverse paths */
	if p`Type eq "LineSegment" then
		q := CLineSegment(p`EndPt,p`StartPt);
	elif p`Type eq "Arc" then
		q := CArc(p`EndPt,p`StartPt,p`Center : o := (-1)*p`Orientation);
	elif p`Type eq "FullCircle" then
		q := CFullCircle(p`StartPt, p`Center : o := (-1)*p`Orientation);
	elif p`Type eq "Point" then
		q := CPoint(p`StartPt);
	end if;

	/* Permutation of reverse path */
	if assigned p`Permutation then
		Sigma := p`Permutation;
		q`Permutation := Inverse(Sigma);
		/* Integrals along reverse path */
		if assigned p`Integrals then
			m := Degree(Parent(Sigma));
			g := NumberOfColumns(p`Integrals);
			q`Integrals := PermuteMatrix(-p`Integrals,q`Permutation,m,g);
		end if;
	end if;
	return q;
end function;

function IsConnectedPath( Paths ) 
/* Checks, if the paths are connected & closed */
	for i in [1..#Paths-1] do
		if Abs(Paths[i]`EndPt-Paths[i+1]`StartPt) gt 10^(-Precision(Parent(Paths[i]`EndPt))/2) then
			print "Path[i]:",Paths[i];
			print "Paths[i]`EndPt:",Paths[i]`EndPt;
			print "Prec Paths[i]`EndPt:",Precision(Paths[i]`EndPt);
			print "Path[i+1]:",Paths[i+1];
			print "Paths[i+1]`StartPt:",Paths[i+1]`StartPt;
			print "Prec Paths[i+1]`StartPt:",Precision(Paths[i+1]`StartPt);
			return false, false;
		end if;
	end for;
	if Paths[1]`StartPt ne Paths[#Paths]`EndPt then
		return true, false;
	else
		return true, true;
	end if;
end function;

/* Class CChain: chains consist of concatinations of paths (CPath) in the complex plane */
declare type CChain;
declare attributes CChain: Paths,Length,Permutation,IsClosed,StartPt,EndPt,Integrals,Center,IndexPathList,Radius,Singularities,Points,Sheets;

/* Constructor */
intrinsic Chain( Paths::SeqEnum[CPath] : Center := "" ) -> CChain
{ Creates a CChain object by concatenating the paths in Paths. }
	//require #Paths gt 0 : "Chain cannot be the empty list.";
	IsConnected, IsClosed := IsConnectedPath( Paths );
	require IsConnected : "Chains have to consist of connected paths.";

	Ch := New(CChain);
	Ch`Paths := Paths;
	Ch`Length := #Paths;
	Ch`IsClosed := IsClosed;
	Ch`StartPt := Paths[1]`StartPt;
	Ch`EndPt := Paths[#Paths]`EndPt;

	if IsClosed and Center cmpne "" then
		Ch`Center := Center;
	end if;

	if &and[ assigned p`Permutation : p in Paths] then
		// Assign permutation
		Ch`Permutation := &*[ p`Permutation : p in Paths ];
		m := Degree(Parent(Ch`Permutation));
		if &and[ assigned p`Integrals : p in Paths ] then
			// Assign integrals
			g := NumberOfColumns(Paths[1]`Integrals);
			C<I> := BaseRing(Parent(Paths[1]`Integrals));
			Ch`Integrals := Matrix(C,m,g,[]);
			Sigma := Id(Parent(Ch`Permutation));
			for k in [1..Ch`Length] do
				Ch`Integrals +:= ChangeRing(PermuteMatrix(Ch`Paths[k]`Integrals,Sigma,m,g),C);
				Sigma *:= Ch`Paths[k]`Permutation;
			end for;
		end if;
	end if;
	return Ch;
end intrinsic;

intrinsic Print( Ch::CChain : Precision := 10 )
{ Printing. }
	C<I> := ComplexField(Precision);
	if #Ch`Paths eq 0 then
		print "Empty chain.";
	elif Ch`IsClosed then
		if assigned Ch`Center then
			if Type(Ch`Center) eq FldComElt then
				print "Closed chain consisting of",Ch`Length,"paths starting at",C!Ch`StartPt,"around",C!Ch`Center;
			else
				print "Closed chain consisting of",Ch`Length,"paths starting at",C!Ch`StartPt,"around",Ch`Center;
			end if;
		else
			print "Closed chain consisting of",Ch`Length,"paths starting at",C!Ch`StartPt;
		end if;
	else
		print "Chain consisting of",Ch`Length,"paths from",C!Ch`StartPt,"to",C!Ch`EndPt;
	end if;
	if assigned Ch`Permutation then
		print "Permutation:",Ch`Permutation;
	end if;
	if assigned Ch`Integrals then
		print "Integrals:",assigned Ch`Integrals;
	end if;
end intrinsic;


/* Define "=" for type CChain */
intrinsic 'eq'( Ch1::CChain, Ch2::CChain ) -> BoolElt
{ Returns true, if Ch1 and Ch2 consist of the same paths, false otherwise. }
	return Ch1`Paths eq Ch2`Paths;
end intrinsic;

/* Define "*" for type CChain Careful: ***NOT ABELIAN*** */
intrinsic '*'( Ch1::CChain, Ch2::CChain ) -> CChain
{ If possible, concatinate the chains Ch1 and Ch2 }
	ResCh := Chain(Ch1`Paths cat Ch2`Paths);	
	if assigned Ch1`Permutation and assigned Ch2`Permutation and not assigned ResCh`Permutation then
		ResCh`Permutation := Ch1`Permutation * Ch2`Permutation;
		if assigned Ch1`Integrals and assigned Ch2`Integrals and not assigned ResCh`Integrals then
			ResCh`Integrals := [ Ch1`Integrals[j] + PermuteVector(Ch2`Integrals[j],Ch1`Permutation,Degree(Parent(Ch1`Permutation))) : j in [1..#Ch1`Integrals] ];
		end if;
	end if;
	return ResCh;
end intrinsic;

/* Define "^" for typ CChain */
intrinsic '^'( Ch::CChain, k::RngIntElt ) -> CChain
{ Multiply closed chains by integers != 0}
	if Abs(k) ne 1 then
		require Ch`IsClosed : "Only closed chains can be taken to integers powers of absolute value > 1.";
	end if;
	if k eq 0 then
		ResCh := Chain(Point(Ch`StartPt));
	end if;
	if Sign(k) eq 1 then
		ResCh := Ch;
		for j in [1..k-1] do
			ResCh *:= Ch;
		end for;		
	else
		ResCh_ := Chain(Reverse([ ReversePath(p) : p in Ch`Paths ]));
		if not assigned ResCh_`Permutation and assigned Ch`Permutation then
			ResCh_`Permutation := Ch`Permutation^(-1);
			if assigned Ch`Integrals and not assigned ResCh_`Integrals then
				ResCh_`Integrals := [ ResCh_`Permutation * ((-1) * Ch`Integrals[j]) : j in [1..#Ch`Integrals] ];
			end if;
		end if;
		ResCh := ResCh_;
		for j in [1..Abs(k)-1] do
			ResCh *:= ResCh_;
		end for;
	end if;
	return ResCh;
end intrinsic;

/* Geometry in the complex plane */
function OrthogonalProjection( LS, FCCenter )
return LS`StartPt + ( ( Re(FCCenter - LS`StartPt) * Re(LS`EndPt - LS`StartPt) + Im(FCCenter - LS`StartPt) * Im(LS`EndPt - LS`StartPt ) ) / ( (LS`EndPt - LS`StartPt) * Conjugate(LS`EndPt - LS`StartPt) ) ) * (LS`EndPt - LS`StartPt);
end function;
function LSIntersectFC( LS, FC )
/* Checks for intersections between the LineSegment LS and the FullCircle FC using orthogonal projection */
	OrthProj := OrthogonalProjection( LS, FC`Center );
	DistMax := Abs(LS`StartPt-LS`EndPt);
	DistProj := Abs(LS`StartPt-OrthProj);
	if DistProj le DistMax then
		Ratio := DistProj/DistMax;
		Value := LS`Evaluate(2*Ratio-1);
		if Abs(Value-OrthProj) lt 10^(-Precision(Value)/2) then
			DistToCenter := Abs(FC`Center-OrthProj);
			if DistToCenter le FC`Radius then
				return true, OrthProj;
			end if;
		end if;
	end if;
	return false, _;
end function;
function IntersectionPoints( LS, FC )
/* Computes potential intersection points between the infinite line defined by LineSegment and the FullCircle FC */
	assert LS`Type eq "LineSegment";
	assert FC`Type eq "FullCircle";
	OK, OrthProj := LSIntersectFC(LS,FC);
	if OK then
		IntPoints := [];
		DistToCenter := Abs(FC`Center-OrthProj);
		DistOrthProj := Abs(LS`StartPt-OrthProj);
		b := SquareRoot(FC`Radius^2 - DistToCenter^2);
		if not IsReal(b) then
			error Error("Error in function IntersectionPoints.");
		end if;
		/* First point */
		DistFirstPoint := DistOrthProj - b;
		DistMax := Abs(LS`EndPt-LS`StartPt);
		if Abs(DistFirstPoint) lt 10^(-Precision(LS`StartPt)/2) then
			IntPoints[1] := LS`StartPt;
		else
			r1 := DistFirstPoint/DistMax;
			IntPoints[1] := LS`Evaluate(2*r1-1);
		end if;
		/* Second point */
		DistSecondPoint := DistOrthProj + b;
		r2 := DistSecondPoint/DistMax;
	 	IntPoints[2] := LS`Evaluate(2*r2-1);
		if Abs(IntPoints[1]-LS`StartPt) le Abs(IntPoints[2]-LS`StartPt) then
			return true, IntPoints;
		else	
			return true, Reverse(IntPoints);
		end if;
	else 
		return false, [];
	end if;
end function;

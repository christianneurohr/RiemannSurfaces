function EmbedPolynomial( f,P,Cxy )
/* Embed an RngMPol defined over a number field using the infinite place P into the complex */
	assert IsInfinite(P);
	C_f := Coefficients(f); 
	M_f := Monomials(f);
	f := &+[ Evaluate(C_f[j],P:Precision:=Precision(BaseRing(Cxy)))*Cxy!M_f[j] : j in [1..#M_f] ];
	return f;
end function;

function IsWeaklyIn( P,L,Err )
/* Checks whether P is in L up to an error of Err */
	if #L eq 0 then
		return false,_;
	end if;
	p := #P;
	assert p eq #L[1];
	for k in [1..#L] do
		if &and[ Abs(P[l]-L[k][l]) lt Err : l in [1..p] ] then
			return true, k;
		end if;
	end for;
	return false, _;
end function;

function CompareByFirstEntry(x,y)
	if x[1] lt y[1] then 
		return -1;
	elif x[1] eq y[1] then 
		return 0; 
	else 
		return 1; 
	end if;
end function;

function CompareFldComElt(x,y)
	Err := Real(10^-(Precision(Parent(x))/2));
	if Abs(Re(x)-Re(y)) gt Err then
		if Re(x) lt Re(y) then 
			return -1;
		elif Re(x) gt Re(y) then 
			return 1;
		end if;
	elif Abs(Im(x)-Im(y)) gt Err then
		if Im(x) lt Im(y) then 
			return -1;
		elif Im(x) gt Im(y) then 
			return 1; 
		end if; 
	else
		return 0;
	end if;
end function;

function CompareByFirstComplexEntry(x,y)
	return CompareFldComElt(x[1],y[1]);
end function;

function IntGroups_SE(IntParPaths,rm,m)
	if m gt 2 then
		Groups := [ [],[],[] ];
		for r in IntParPaths do
			if r lt rm+0.5 then Append(~Groups[1],r);
			elif r lt rm+1.5 then Append(~Groups[2],r);
			else Append(~Groups[3],r); end if;
		end for;
	else
		Groups := [ [],[],[],[],[],[] ];
		for r in IntParPaths do if r lt rm+0.1 then Append(~Groups[1],r); elif r lt rm+0.2 then Append(~Groups[2],r);
			elif r lt rm+0.4 then Append(~Groups[3],r);
			elif r lt rm+0.8 then Append(~Groups[4],r);
			elif r lt rm+1.6 then Append(~Groups[5],r);
			else Append(~Groups[6],r); end if;
		end for;
	end if;
	return Groups;
end function;
function IntGroups(IntParPaths,rm,IntMethod)
	if IntMethod eq "GL" then
		Groups := [ [],[],[],[],[] ];
		for r in IntParPaths do
			if r lt rm+0.1 then Append(~Groups[1],r); elif r lt rm+0.4 then	Append(~Groups[2],r);
			elif r lt rm+0.9 then Append(~Groups[3],r); elif r lt rm+2.0 then Append(~Groups[4],r);
			else Append(~Groups[5],r); end if;
		end for;
	elif IntMethod eq "CC" then
		Groups := [ [],[],[],[],[],[],[],[],[] ];
		for r in IntParPaths do if r lt rm+0.1 then Append(~Groups[1],r); elif r lt rm+0.2 then Append(~Groups[2],r);
			elif r lt rm+0.3 then Append(~Groups[3],r); elif r lt rm+0.4 then Append(~Groups[4],r);
			elif r lt rm+0.6 then Append(~Groups[6],r); elif r lt rm+0.9 then Append(~Groups[7],r);
			elif r lt rm+2.0 then Append(~Groups[8],r);
			else Append(~Groups[9],r); end if;
		end for;
	else 
		error Error("Invalid integration method.");
	end if;
	return Groups;
end function;

function SortByRealPart(V)
	oV := []; up := 0;
	for z in V do
		if Re(z) le 0 then
			Append(~oV,z);	
		else
			Insert(~oV,1,z);
			up +:= 1;
		end if;
	end for;
	return oV,up;
end function;

procedure PolynomialShiftVector( ~V, c, Len, Shft )
/* returns (v0, c*v0 + v1, c^2*v0 + 2c*v1 + v2, ...) */
	for k in [2..Len] do
		l := Len;
		while l ge k do
			V[l+Shft] +:= c * V[l+Shft-1];
			l -:= 1;
		end while;
	end for;
end procedure;

/*function DistanceII(Points)
	Distances := [];
	L := #Points;
	for k in [1..L] do
		for l in [k+1..L] do
			Append(~Distances,Abs(Points[k]-Points[l]));
		end for;
	end for;
	return Min(Distances);
end function;*/

function SE_DKPEB(f,Z,Digits)
/* Iterate the simple roots of a polynomial to precision Digits */
	f := ChangeRing(f/LeadingCoefficient(f),ComplexField(2*Digits));
	Z := ChangeUniverse(Z,ComplexField(2*Digits));
	m := Degree(f);
	RMV := [ Remove([1..m],j) : j in [1..m] ];
	Err2 := (1/2) * 10^-(Digits+1);
	W := [ Evaluate(f,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
	repeat
		Z := [ Z[j] - W[j] : j in [1..m] ];
		W := [ Evaluate(f,Z[j])/ &*[ (Z[j] - Z[k]) : k in RMV[j] ] : j in [1..m] ];
		w0 := Max([ Abs(W[j]) : j in [1..m] ]);
	until w0 lt Err2;
	return Z;
end function;

function ModifiedRoots( g : Prec := -1 )
/* Return the roots of the complex polynomial g with precision Prec */
	assert Degree(g) gt 0;
	if Prec lt 0 then
		Prec := Precision(BaseRing(Parent(g)));
	end if;
	g *:= 1/LeadingCoefficient(g);
	CoeffAbs := [ Abs(c):c in Coefficients(g) | c ne 0 ]; 
	/* Upper bound for roots */
	MaxCH := Ceiling(Max([Log(10,1+c) : c in CoeffAbs ]));
	MinCH := Abs(Floor(Log(10,Min(CoeffAbs))));
	MinPrec := Prec + 2 * Max(MaxCH,MinCH);
	g := ChangeRing(g,ComplexField(MinPrec));
	Rts := Roots(g);
	Rts := &cat[ [ r[1] : j in [1..r[2]] ] : r in Rts ];
	assert #Rts eq Degree(g);
	Sort(~Rts,CompareFldComElt);
	return ChangeUniverse(Rts,ComplexField(Prec));
end function;

function ModifiedFiber( f, x0 : Prec := -1 )
/* Return the the roots of f(x0,y) to precision Prec */
	return ModifiedRoots(Evaluate(f,[x0,PolynomialRing(Parent(x0)).1]) : Prec := Prec);
end function;

intrinsic RandomSuperellipticRiemannSurface( m::RngIntElt, n::RngIntElt : Ht := 10^5, Monic := false, Prec := 30, Exact := true ) -> RngMPolElt
{ Returns a random hyperelliptic curve given as multivariate polynomial}
	if Exact then
		Qx<x> := PolynomialRing(Rationals());
		if Monic then
			f := x^n;
		else
			f := Random([-1,1])*Random([1..Ht])*x^n;
		end if;
		for j in [0..n-1] do
			c := Random([-1,0,1]);
			f +:= c*Random([1..Ht])*x^j;
		end for;
		if Gcd(f,Derivative(f)) eq One(Qx) then
			return RandomSuperellipticRiemannSurface(m,n: Prec := Prec, Ht :=Ht, Monic := Monic, Exact:=Exact );
		end if;
	else
		C<I> := ComplexField(Prec);
		Cx<x> := PolynomialRing(C);
		if Monic then
			f := x^n;
			nn := n-1;
		else
			f := 0;
			nn := n;
		end if;
		for j in [0..nn] do
			c := Random([-Ht..Ht])/Random([1..Ht]) + I*Random([-Ht..Ht])/Random([1..Ht]);
			f +:= Random([-1..1])*c*x^j;
		end for;
		if #Roots(f) ne n then
			return RandomSuperellipticRiemannSurface(m,n: Prec := Prec, Ht :=Ht, Monic := Monic, Exact:=Exact );
		end if;
	end if;
	print "f:",f;
	return RiemannSurface(f,m);
end intrinsic;

intrinsic RandomRiemannSurface( DegX::RngIntElt , DegY::RngIntElt : Ht := 10^5 ,Sparse := Random([0..(DegX+1)*(DegY+1)-3]), NFDeg := 1 ) -> RngMPolElt
{ Returns a random polynomial defining a Riemann surface }
	if NFDeg gt 1 then
		Z<z> := PolynomialRing(Rationals());
		while true do
			g := Z![ Random([-1,1])*Random([1..Ht]) : j in [1..NFDeg+1] ];
			if IsIrreducible(g) then
				break;
			end if;
		end while;
		K := NumberField(g);
	else
		K := RationalsAsNumberField();
	end if;
	Kxy<x,y> := PolynomialRing(K,2);
	f := Zero(Kxy);
	assert Sparse lt (DegX+1)*(DegY+1)-2;
	SparseSet := {};
	while #SparseSet lt Sparse do
 		SparseSet join:= { <Random([0..DegX]),Random([0..DegY])> };
	end while;
	for j in [0..DegX] do
		for k in [0..DegY] do
			if <j,k> notin SparseSet then
				f +:= Random(K,Ht)*x^j*y^k;
			end if;
		end for;
	end for;
	A := AffineSpace(K,2);
	Cu := Curve(A,f);
	if IsAbsolutelyIrreducible(Cu) and Genus(ProjectiveClosure(Cu)) gt 0 then
		return f;
	else
		return RandomRiemannSurface( DegX, DegY : Ht := Ht, Sparse := Sparse, NFDeg := NFDeg);
	end if;
	return f;
end intrinsic;

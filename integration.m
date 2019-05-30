/*******************************************************************************

	Numerical integration routines
 
	Christian Neurohr, September 2018

*******************************************************************************/

import "paths.m": CLineSegment;
import "miscellaneous.m": ModifiedFiber, PolynomialShiftVector;

NAIVEBOUND := 10^5;
RPI := Pi(RealField(30));

/* Define type for numerical integration: IntScheme */
declare type IntScheme;
declare attributes IntScheme: Abscissas, Weights, ExtraWeights, N, Bounds, IntPar, Type, Prec, AlphaBeta, Params;

/* Printing */
intrinsic Print(IntSch::IntScheme)
{ Printing. }
	print "Integration type:",IntSch`Type;
	print "Number of abscissas:",IntSch`N;
	print "Precision:",IntSch`Prec;
	if assigned IntSch`IntPar then
		print "IntPar:",IntSch`IntPar;
	end if;
	if assigned IntSch`IntPar then
		print "Bounds:",IntSch`Bounds;
	end if;
end intrinsic;

function DE_IntegrationParameters( r, Prec : Bounds := [NAIVEBOUND,NAIVEBOUND], Lambda := Pi(Parent(r))/2 )
/* Computes integration parameters N and h for double exponential integration on the interval [-1,1] */
	/* Real field of maximal precision */
	R := Parent(r);	
	/* Compute D */
	D := R!(Prec * Log(10));
	/* Bounds M_1 and M_2 */
	M_1 := R!Bounds[1];
	M_2 := R!Bounds[2];
	X_r := Cos(r) * Sqrt( Pi(R)/(2*Lambda*Sin(r)) - 1 ); 
	/* B(r,\alpha) */
	B_r := (2/Cos(r)) * ( (X_r/2) * (1/((Cos(Lambda*Sin(r)))^2) + 1/(X_r^2)) + 1/(2*Sinh(X_r)^2) ); 
	/* Compute steplength h */
	h := (2 * Pi(R) * r ) / ( D + Log( 2*M_2*B_r + Exp(-D) ));
	/* Compute #integration points = 2*N+1 */ 
	N := Ceiling(Argsinh( (D+ Log(8*M_1))/(2*Lambda)) / h );
	return N, h;
end function;

function DE_Integration( r, Prec : Bounds := [NAIVEBOUND,NAIVEBOUND], Lambda := Pi(Parent(r))/2 )
/* Computes a double-exponential integration scheme */
	DE_Int := New(IntScheme);
	DE_Int`Type := "DE";
	DE_Int`Prec := Precision(r);
	assert Precision(r) ge Prec;
	assert r lt RPI/2;
	assert r gt 0;
	DE_Int`Bounds := Bounds;
	N,h := DE_IntegrationParameters( r, Prec : Bounds := Bounds, Lambda := Lambda );
	assert Precision(h) eq Precision(r);
	DE_Int`Abscissas, DE_Int`Weights := TanhSinhIntegrationPoints( N, h );
	DE_Int`N := 2*N+1;
	DE_Int`IntPar := ChangePrecision(r,10);
	return DE_Int;
end function;

intrinsic TanhSinhIntegrationPoints( N::RngIntElt, h::FldReElt : Lambda:=Pi(Parent(h))/2 ) -> SeqEnum[FldReElt], SeqEnum[FldReElt]
{ Computes integration parameters for double exponential integration on the interval [-1,1] }

	// Precision of only depens on Precision(h)
	R := Parent(h);
	eh := Exp(h); // e^h
	eh_inv := 1/eh; // e^-h
	ekh := 1; // e^0h
	ekh_inv := 1; // e^-0h
	Abscissas_ := [];
	Weights_ := [];
	lh := Lambda * h;
	oh := One(R)/2;
	for k in [1..N] do
		ekh *:= eh; // e^kh
		ekh_inv *:= eh_inv; // e^-kh
     		sh := oh*(ekh-ekh_inv); // sinh(kh) = (1/2) * (e^kh - e^-kh)
		ch := sh+ekh_inv; // cosh(kh) = (1/2) * (e^kh + e^-kh)
      		//ch2 := (ekh+ekh_inv); //  2*cosh(kh) = (e^kh + e^-kh)
      		esh := Exp(Lambda*sh); // e^(Lambda*sinh(kh))
      		esh_inv := 1/esh; // e^-(Lambda*sinh(kh))
		chsh_inv := 2/(esh+esh_inv); // 1/cosh(Lambda*sinh(kh)))
      		//chsh2_inv := 1/(esh+esh_inv); // 1/(2*cosh(Lambda*sinh(kh)))
		shsh := oh*(esh-esh_inv); // sinh(Lambda*sinh(kh))
      		//shsh2 := esh-esh_inv; // 2*sinh(Lambda*sinh(kh))
		thsh := shsh*chsh_inv; // tanh(Lambda*sinh(kh)) =  sinh(Lambda*sinh(kh)) / cosh(Lambda*sinh(kh))
      		//thsh := shsh2*chsh2_inv; // tanh(Lambda*sinh(kh)) =  2*sinh(Lambda*sinh(kh)) / 2*cosh(Lambda*sinh(kh))
		Append(~Abscissas_,thsh);
		Append(~Weights_,ch*chsh_inv*chsh_inv*lh); // = cosh(kh) / cosh(Lambda*sinh(kh))^2
		//Append(~Weights_,2*ch2*chsh2_inv^2); // = 2*2*cosh(kh) / 4*(cosh(Lambda*sinh(kh)))^2
     	end for;

	Abscissas := Reverse([-zk : zk in Abscissas_]) cat [0] cat Abscissas_;
	Weights  := Reverse(Weights_) cat [lh] cat Weights_;

  	return Abscissas, Weights;
end intrinsic;

function DistanceToBurger(x,r: Lambda := RPI/2, ss:=20 )
	C := Parent(x);
	Phi := function(t)
		return Tanh(Lambda*Sinh(t+C.1*r));
	end function;
	if Abs(Re(x)) lt 10^-10 then
		xr := Sign(Im(x)) * Phi(0);
		return xr, Abs(x-xr);
	end if;
	xt := Abs(Re(x)) + C.1 * Abs(Im(x));
	tmax := Argcosh(Pi(C)/(2*Lambda*Sin(r)));
	xr := Phi(0);
	MinDist := Abs(xt-xr);
	for k in [1..ss] do
		t := k/ss*tmax;
		z := Phi(t);
		Dist := Abs(xt-z);
		if Dist lt MinDist then
			MinDist := Dist;
			xr := z;
		end if;
	end for;
	if Abs(Im(x)) lt 10^-10 then
		xr := Sign(Re(x)) * Re(xr) + C.1 * Im(xr);
	else
		xr := Sign(Re(x)) * Re(xr) + C.1 * Sign(Im(x))*Im(xr);
	end if;
	return xr, MinDist;
end function;	

function DE_Params_LineSegment( Points, Gamma : Lambda := RPI/2 )
	TauGamma := 5.0;
	for k in [1..#Points] do
		u_k := (2*Points[k]-Gamma`EndPt-Gamma`StartPt)/(Gamma`EndPt-Gamma`StartPt);
		r_k := Abs(Im(Argsinh(Argtanh(u_k)/Lambda)));
		if r_k lt TauGamma then
			TauGamma := r_k;
			Gamma`WP := u_k;
		end if;
	end for;
	return TauGamma;
end function;
function DE_Params_Arc( Points, Gamma : Lambda := RPI/2 )
	C := Universe(Points);
	TauGamma := 5.0;
	for k in [1..#Points] do
		if Points[k] ne Gamma`Center then
			u_k := (Gamma`Orientation/(Gamma`EndArg-Gamma`StartArg)) * (-2 * C.1 * Log((Points[k]-Gamma`Center)/(Gamma`Radius*Exp(C.1*(Gamma`EndArg + Gamma`StartArg)/2))));
			r_k := Abs(Im(Argsinh(Argtanh(u_k)/Lambda)));
			if r_k lt TauGamma then
				TauGamma := r_k;
				Gamma`WP := u_k;
			end if;
		end if;
	end for;
	while Abs((Gamma`EndArg-Gamma`StartArg)*Im(Tanh(Lambda*Sinh(-C.1*TauGamma)))) ge 2*Real(Pi(C)) do
			TauGamma -:= (1/20);
	end while;
	return TauGamma;
end function;
function DE_Params_FullCircle( Points, Gamma : Lambda := RPI/2 )
	C := Universe(Points);
	TauGamma := 5.0;
	for k in [1..#Points] do
		if Points[k] ne Gamma`Center then
			u_k := -Gamma`Orientation/Pi(C) * C.1 * Log((Gamma`Center-Points[k])/(Gamma`Radius*Exp(C.1*Gamma`StartArg)));
			r_k := Abs(Im(Argsinh(Argtanh(u_k)/Lambda)));
			if r_k lt TauGamma then
				TauGamma := r_k;
				Gamma`WP := u_k;
			end if;
		end if;
	end for;
	while Abs(Im(Tanh(Lambda*Sinh(-C.1*TauGamma)))) ge 1 do
			TauGamma -:= 1/20;
	end while;
	return TauGamma;	
end function;
function DE_Params_InfiniteLine( Points, Gamma : Lambda := RPI/2 )
	TauGamma := 5.0;
	for k in [1..#Points] do
		if Abs(Points[k]) gt 10^(-Precision(Lambda)/2) then 
			u_k := -(2*Gamma`StartPt/Points[k]) + 1;
			r_k := Abs(Im(Argsinh(Argtanh(u_k)/Lambda)));
			if r_k lt TauGamma then
				TauGamma := r_k;
				Gamma`WP := u_k;
			end if;
		end if;
	end for;
	return TauGamma;
end function;
procedure DE_Params_Path( Points, Gamma )
/* Double-exponential integration: compute the parameter r for the path Gamma */
	if not assigned Gamma`IntPar then
		Gamma`IntMethod := "DE";
		if Gamma`Type eq "LineSegment" then
			Gamma`IntPar := DE_Params_LineSegment( Points, Gamma ); 
			Gamma`Subpaths := [Gamma];
		elif Gamma`Type eq "Arc" then
			Gamma`IntPar := DE_Params_Arc( Points, Gamma );
			Gamma`Subpaths := [Gamma];
		elif Gamma`Type eq "FullCircle" then
			Gamma`IntPar := DE_Params_FullCircle( Points, Gamma );
			Gamma`Subpaths := [Gamma];
		elif Gamma`Type eq "InfiniteLine" then
			Gamma`IntPar := DE_Params_InfiniteLine( Points, Gamma );
		elif Gamma`Type eq "Point" then
			Gamma`IntPar := 1.5;
		else
			error Error("Invalid path type.");
		end if;
	end if;
end procedure;

function DistanceToEllipse(x,r)
/* Approximates a point on the ellipse parametriyed by r>1 that minimizes the distance to the complex number x */
	C<I> := Parent(x);
	assert r gt 1;
	/* if x is real, return +-cosh(r) */
	if Abs(Im(x)) lt 10^-10 then
		xr := Sign(Re(x))*r;
		return xr,Abs(x-xr);
	end if;
	b := Sqrt(r^2-1);
	/* if x is imaginary, return +-I*b */
	if Abs(Re(x)) lt 10^-10 then
		xr := Sign(Im(x))*b*I;
		return xr,Abs(x-xr);
	end if;
	/* otherwise, save signs */
	ImSgn := Sign(Im(x));
	ReSgn := Sign(Re(x));
	/* and take x to be in the first quadrant */
	x := Abs(Re(x)) + I*Abs(Im(x));
	function s(t)
		return Cos(t)*Sin(t)-r*Re(x)*Sin(t)+b*Im(x)*Cos(t);
	end function;
	function sp(t)
		return (Cos(t)^2 - Sin(t)^2) - r*Re(x)*Cos(t) - b*Im(x)*Sin(t);
	end function;
	t := Re(Arccos(x));
	repeat
		nt := t;
		t -:= s(t)/sp(t);
	until Abs(t-nt) lt 10^-3;
	xr := r*Cos(t)+I*b*Sin(t);
	return ReSgn*Re(xr)+I*ImSgn*Im(xr),Abs(x-xr);
end function;

function ClenshawCurtisParameters(r,Err:Bound:=NAIVEBOUND)
	R := RealField(10);
	achr := Argcosh(r);
	N := Ceiling((Log(64*R!Bound/15)-Log(R!Err)-Log(1-Exp(achr)^(-2)))/achr)-1;
	return N;
end function;
function GaussLegendreParameters(r,Err:Bound:=NAIVEBOUND)
	R := RealField(10);
	achr := Argcosh(r);
	N := Ceiling((Log(64*R!Bound/15)-Log(R!Err)-Log(1-Exp(achr)^(-2)))/(2*achr));
	return N;
end function;
function GLCC_Params_LineSegment( Points, Gamma )
	C := Universe(Points);
	r_0 := 5.0;
	GP := ChangeUniverse([Gamma`StartPt,Gamma`EndPt],C);
	for k in [1..#Points] do
		if Points[k] notin GP then
			u_k := (2*Points[k] - Gamma`StartPt - Gamma`EndPt) / (Gamma`EndPt - Gamma`StartPt);
			r_k := (1/2) * ( Abs(u_k+1) + Abs(u_k-1) );
			assert r_k gt 1;
			if r_k lt r_0 then
				r_0 := r_k;
				Gamma`WP := u_k;
			end if;
		end if;
	end for;
	if r_0 eq 5.0 then
		Append(~Gamma`Bounds,1);
	end if;
	return r_0;
end function;
function GLCC_Params_Arc( Points, Gamma )
	C := Universe(Points);
	RPi := Real(Pi(C));
	r_0 := 5.0;
	GP := ChangeUniverse([Gamma`EndArg,Gamma`StartArg,Gamma`Center,Gamma`Radius],C);
	for k in [1..#Points] do
		if Points[k] ne GP[3] then
			u_k := (Gamma`Orientation/(GP[2]-GP[1])) * (-2*C.1*Log((Points[k]-GP[3])/(GP[4]*Exp(C.1*(GP[2] + GP[1])/2))));
			r_k := (1/2) * ( Abs(u_k+1) + Abs(u_k-1) );
			assert r_k gt 1;
			if r_k lt r_0 then
				r_0 := r_k;
				Gamma`WP := u_k;
			end if;
		end if;
	end for;
	if r_0 eq 5.0 then
		Append(~Gamma`Bounds,1);
	end if;
	return r_0;
end function;
function GLCC_Params_FullCircle( Points, Gamma )
	C := Universe(Points);
	RPi := Real(Pi(C));
	r_0 := 5.0;
	for k in [1..#Points] do
		if Points[k] ne Gamma`Center then
			u_k := -Gamma`Orientation/RPi * C.1 * Log((Gamma`Center-Points[k])/(Gamma`Radius*Exp(C.1*Gamma`StartArg)));
			r_k := (1/2) * ( Abs(u_k+1) + Abs(u_k-1) );
			assert r_k gt 1;
			if r_k lt r_0 then
				r_0 := r_k;
				Gamma`WP := u_k;
			end if;
		end if;
	end for;
	if r_0 eq 5.0 then
		Append(~Gamma`Bounds,1);
	end if;
	return r_0;
end function;
function SplitLineSegment( Points, Gamma, Err, IntMethod )
/* Splits line segments into subpaths in order to improve Gauss-Legendre/Clenshaw-Curtis integration */
	if not assigned Gamma`IntPar then
		Gamma`IntMethod := IntMethod;
		Gamma`IntPar := GLCC_Params_LineSegment(Points,Gamma);
	end if;
	Paths := [ Gamma ];
	/* Is splitting worh it? */
	if Gamma`IntPar lt 1.2 then
		if Abs(Re(Gamma`WP)) le (3/4) then
			x := Gamma`Evaluate(Parent(Gamma`StartPt)!Re(Gamma`WP));
		else
			x := Gamma`Evaluate(Sign(Re(Gamma`WP))*(3/4));
		end if;
		Gam1 := CLineSegment(Gamma`StartPt,x); 
		Gam1`IntMethod := IntMethod;
		Gam2 := CLineSegment(x,Gamma`EndPt); 
		Gam2`IntMethod := IntMethod;
		Gam1`IntPar := GLCC_Params_LineSegment(Points,Gam1);
		Gam2`IntPar := GLCC_Params_LineSegment(Points,Gam2);
		if IntMethod in ["GL","GLDE"] then 
			Gamma`N := GaussLegendreParameters(Gamma`IntPar,Err);
			Gam1`N := GaussLegendreParameters(Gam1`IntPar,Err);
			Gam2`N := GaussLegendreParameters(Gam2`IntPar,Err);
		elif IntMethod in ["CC","CCDE"] then
			Gamma`N := ClenshawCurtisParameters(Gamma`IntPar,Err);
			Gam1`N := ClenshawCurtisParameters(Gam1`IntPar,Err);
			Gam2`N := ClenshawCurtisParameters(Gam2`IntPar,Err);
		else
			error Error("Invlaid integration method.");
		end if;
		if Gamma`N-Gam1`N-Gam2`N ge 10 then
			vprint RS,2 : "Splitting line segment saves",Gamma`N-Gam1`N-Gam2`N,"integration points!";
			Paths := SplitLineSegment(Points,Gam1,Err,IntMethod) cat SplitLineSegment(Points,Gam2,Err,IntMethod);
		end if;
		return Paths;
	else
		return Paths;
	end if;
end function;
procedure GLCC_Params_Path( Points,  Gamma, Err, IntMethod )
/* Gauss-Legendre/Clenshaw-Curtis compute the parameter r for the path Gamma */
	Gamma`IntMethod := IntMethod;
	if not assigned Gamma`IntPar then
		if Gamma`Type eq "LineSegment" then
			Gamma`Subpaths := SplitLineSegment(Points,Gamma,Err,IntMethod);
		elif Gamma`Type eq "Arc" then	
			Gamma`IntPar := GLCC_Params_Arc(Points,Gamma); 
			Gamma`Subpaths := [ Gamma ];
		elif Gamma`Type eq "FullCircle" then
			Gamma`IntPar := GLCC_Params_FullCircle(Points,Gamma); 
			Gamma`Subpaths := [ Gamma ];		
		elif Gamma`Type eq "Point" then
			Gamma`IntPar := 5.0;
		else
			error Error("Invalid path type.");
		end if;
	end if;
end procedure;

function GL_Integration( r, Prec, Err : Bound := NAIVEBOUND )
/* Computes a Gauss-Legendre integration scheme */
	/* Create integration scheme */
	GL_Int := New(IntScheme);
	GL_Int`Type := "GL";
	GL_Int`Prec := Prec;
	assert r gt 1;
	GL_Int`IntPar := r;
	GL_Int`Bounds := [Bound];
	N := GaussLegendreParameters(r,Err:Bound:=Bound);
	/* Compute integration points */
	GL_Int`Abscissas, GL_Int`Weights := GaussLegendreIntegrationPoints(N,Prec);
	GL_Int`N := N;
	return GL_Int;
end function;

function GL_REC( N, Prec )
/* REC algorithm for the computation of the Gauss-Legendre integration scheme */
	
	Err := 10^-(Prec+1);
	m := Ceiling((N-1)/2);
	sp := 40;
	RL := RealField(sp);
	N12Pi := Pi(RL)/(N+(1/2));
	c1 := RL!(N-1)/(8*N^3);
	c2 := RL!1/(384*N^4);
	c3 := RL!8*(N+1/2)^2;
	a0 := 0.682894897349453; a1 := 0.131420807470708; a2 := 0.245988241803681; a3 := 0.813005721543268;
	b1 := 0.116837242570470; b2 := 0.200991122197811; b3 := 0.650404577261471;
	function Guess(k)
		pk := N12Pi*(k-(1/4));
		if 3*pk ge Pi(RL) then
			xk := (1-c1-c2*(39-(28/(Sin(pk)^2))))*Cos(pk);
		else
			betas := [ (k-1/4)*Pi(RL) ];
			for j in [1..6] do
				Append(~betas,betas[j]*betas[1]);
			end for;
			jk := betas[1] + (a0 + a1*betas[2] + a2*betas[4] + a3*betas[6])/(betas[1] + b1*betas[3] + b2*betas[5] + b3*betas[7]);
			psik := jk/(N+1/2);
			xk := Cos(psik + (psik*Cot(psik)-1)/(c3*psik));
		end if;
		return xk;
	end function;
	R := RealField(Prec);
	RR := RealField(Prec+5);
	Abscissas := [ RR | ]; Weights := [ RR | ]; 
	B := ChangeUniverse([ 2-(1/j) : j in [1..N] ],RR);
	NInv := RR!(1/N); 
	M2NInv := -2*NInv;
	for k in [1..m] do
		xk := RR!Guess(k);
		p := sp;
		fxk := 0;
		IT := 0;
    		repeat
			xk -:= fxk;
			p2 := B[1]*xk;
			p1 := B[2]*(xk*p2-1)+1; 
			for j in [3..N] do
				p3 := p2;
				p2 := p1;
				p1 := B[j]*(xk*p2-p3) + p3;
			end for;
			tmp := xk*p1-p2;
			ppinv := NInv*(xk*xk-1)/tmp;
			fxk := p1*ppinv;
		until Abs(RL!fxk) lt Err;
		Abscissas[k] := xk;
		Weights[k] := M2NInv*ppinv/tmp;
    	end for;
	ChangeUniverse(~Abscissas,R);
	ChangeUniverse(~Weights,R);
	if N mod 2 eq 1 then
	/* Take 0 into account, if N odd */
		p1 := 1;
		p2 := 0;
		for j in [1..N-1] do
			p3 := p2;
			p2 := p1;
			p1 := (-B[j]+1)*p3;
		end for;
		Abscissas := [ -x : x in Abscissas ] cat [0] cat Reverse(Abscissas);
		Weights := Weights cat [2/((N*p1)^2)] cat Reverse(Weights);
	else
		Abscissas := [ -x : x in Abscissas ] cat Reverse(Abscissas);
		Weights := Weights cat Reverse(Weights);
	end if;
    	return Abscissas,Weights;
end function;

function RungeKuttaMethod(x,theta,f,L:M:=10)
/* Second-order Runge-Kutta method that solves the initial-value problem y(x0) = y0, y'(x) = f(x,y) on the interval [theta,theta+L] in M steps */
	h := L/M;
	for k in [1..M] do
		k1 := h*f(x,theta);
		k2 := h*f(x+k1,theta+h);
		x +:= (1/2)*(k1+k2);
		theta +:= h;
	end for;
	return x;
end function;

function GL_GLR( N, Prec )
/* Glaser-Liu-Rokhlin algorithm for the computation of the Gauss-Legendre integration scheme */

	R := RealField(Prec);
	PrecPlus := Prec+5;
	RR := RealField(PrecPlus);
	sp := 8;
	R10 := RealField(sp);
	Err := 10^-(Prec+1);

	/* Coefficients of differential equation */
	r := N*(N+1);
	mrp2 := -r+2;
	
	/* Number of summands for Taylor series */
	maxm := Min(2*Prec,N+1);
	jInv := [ RR!1/j : j in [1..Max(N,maxm)] ];

	/* ODE, equation (12) */
	function dxdtheta(x,theta)
		pxi := 1/(1-x*x);
		return -1/(Sqrt(pxi*r) - x*pxi * Sin(2*theta)/2);
	end function;
	
	/* Recursion for derivatives of u at xk */
	function duk(x,ukm0,ukm1,m)
		assert m ge 2;
		Derivatives_uk := [ukm0,ukm1];
		pxi := 1/(1-x*x);
		for k in [2..m] do
			Append(~Derivatives_uk,pxi*((k-1)*2*x*Derivatives_uk[k] + (k^2 - 3*k + mrp2 )*Derivatives_uk[k-1]));
		end for;
		return Derivatives_uk;
	end function;
	
	/* Initial root for odd N = 0, initial extrema for even N = 0; Values P_N(0), P'_N(0) as input */
	R0 := Zero(RR);
	if N mod 2 eq 1 then
		/* Compute P'_N(0), Know: P_N(0) = 0 */
		p1 := One(RR);
		p2 := R0;
		for j in [1..N-1] do
			p3 := p2;
			p2 := p1;
			p1 := -(j-1)*p3*jInv[j];
		end for;
		Abscissas := [R0];
		upxk := -N*p1;
		Weights := [ 2/upxk^2 ];
	else
		/* Compute P_N(0), Know: P'_N(0) = 0 */
		p1 := 1;
		p2 := 0;
		for j in [1..N] do
			p3 := p2;
			p2 := p1;
			p1 := -(j-1)*p3*jInv[j];
		end for;

		/* Recursively compute enough derivatives of P at x_e = 0 (for Taylor) */
		Ders_uxk := duk(R0,p1,R0,maxm);
		p := sp;

		/* RungeKutta to find an approximation to x_1 on [0,-Pi/2] */
		xk := RungeKuttaMethod(0.0,0.0,dxdtheta,-Pi(R10)/2:M:=10);

		/* Use Newton-iteration to refine x1 by evaluating P and P' via Taylor expansion */
		m := 10;
		fxk := 0.0;
		repeat 
			m := Min(2*m,maxm);
			p := Min(2*p,PrecPlus);
			xk := ChangePrecision(xk-fxk,p);
			h := xk;
			hk := 1;
			uxk := Ders_uxk[1];
			upxk := 0;
			for k in [2..m] do
				upxk +:= Ders_uxk[k]*hk;
				hk *:= h*jInv[k-1];
				uxk +:= Ders_uxk[k]*hk;
			end for;
			fxk := uxk/upxk;
		until Abs(R10!fxk) lt Err;
		Abscissas := [xk];
		Weights := [ 2/((1-xk^2)*upxk^2) ];
	end if;
	n := Ceiling(N/2);
	theta := Pi(R10)/2;

	for k in [2..n] do
		/* RungeKutta to find an approximation to x_k on [Pi/2,-Pi/2] */
		xkm1 := Abscissas[k-1];

		/* Recursively compute enough derivatives of P at x_{k-1} (for Taylor) */
		Ders_uxk := duk(xkm1,R0,upxk,maxm);

		/* Approximate xk */
		p := sp;
		xk := RungeKuttaMethod(ChangePrecision(xkm1,p),theta,dxdtheta,-Pi(R10):M:=10);
		/* Use Newton-iteration to refine xk by evaluating P and P' via Taylor expansion */
		m := 10;
		fxk := 0.0;
		repeat 
			m := Min(2*m,maxm);
			p := Min(2*p,PrecPlus);
			xk := ChangePrecision(xk-fxk,p);
			h := (xk-xkm1);
			hk := 1;
			uxk := Ders_uxk[1];
			upxk := 0;
			for l in [2..m] do
				upxk +:= Ders_uxk[l]*hk;
				hk *:= h*jInv[l-1];
				uxk +:= Ders_uxk[l]*hk;
			end for;
			fxk := uxk/upxk;
		until Abs(R10!fxk) lt Err;
		Append(~Abscissas,xk);
		Append(~Weights,2/((1-xk^2)*upxk^2));
	end for;
	ChangeUniverse(~Abscissas,R);
	ChangeUniverse(~Weights,R);
	if N mod 2 eq 1 then
		Abscissas := Reverse([ -x : x in Remove(Abscissas,1)]) cat Abscissas;
		Weights := Reverse( Remove(Weights,1) ) cat Weights;
	else
		Abscissas := Reverse([ -x : x in Abscissas]) cat Abscissas;
		Weights := Reverse(Weights) cat Weights;
	end if;
	assert #Abscissas eq N;
	assert #Weights eq N;
	return Abscissas,Weights;
end function;

intrinsic GaussLegendreIntegrationPoints( N::RngIntElt, Prec::RngIntElt ) -> SeqEnum[FldReElt], SeqEnum[FldReElt]
{ Compute the Gauss-Legendre integration scheme on N points in precision Prec. }
	if Prec lt 50 and N ge 250 or
	   Prec le 100 and N ge 300 or 
	   Prec le 200 and N ge 500 or
	   Prec le 300 and N ge 700 or
	   Prec le 500 and N ge 1100 or
	   Prec le 750 and N ge 1900 or
	   Prec le 1000 and N ge 2400 or
	   Prec le 2000 and N ge 5400 then
		return GL_GLR(N,Prec);
	else
		return GL_REC(N,Prec);
	end if;
end intrinsic;


function CC_Integration( r, Prec, Err : Bound := NAIVEBOUND )
/* Computes a Clenshaw-Curtis integration scheme */
	/* Create integration scheme */
	CC_Int := New(IntScheme);
	CC_Int`Type := "CC";
	CC_Int`Prec := Prec;
	assert r gt 1;
	CC_Int`IntPar := r;
	CC_Int`Bounds := [Bound];
	N := ClenshawCurtisParameters(r,Err);
	N := 4 * Ceiling(N/4);
	CC_Int`N := N+1;
	/* Compute N+1 integration points using the FFT */
	CC_Int`Abscissas, CC_Int`Weights := ClenshawCurtisIntegrationPoints(N,Prec);
	return CC_Int;
end function;


intrinsic DiscreteFourierTransform(X::SeqEnum[FldComElt]) -> SeqEnum[FldComElt]
{ Fast-Fourier-Transform of the complex numbers in X. }
	C<I> := Universe(X);
	m2PII := -2*Pi(C)*I;
	N := #X;
	NFac := Factorization(N); NNF := #NFac;
	vprint RS,2 : "NFac:",NFac;
	
	if NFac[1][1] eq 2 then
		PO2 := NFac[1][2];
	else
		PO2 := 0;
	end if;
	/* Use Bluestein? */
	UBS := []; UBS[2] := false; NPO2 := PO2;
	for k in [1..NNF] do
		p := NFac[k][1];
		if p gt 200 then
			UBS[p] := true;
		else
			UBS[p] := false;
		end if;
		if UBS[p] then
			NPO2 := Max(NPO2,Ceiling(Log(2,p))+1);
		end if;
	end for;

	/* Compute Zetas */
	ZetasNPrimes := [];
	procedure ComputeZetas(~ZNP,p,s)
		pss := 1; pm1 := p-1;
		ZNP[p] := [];
		if p eq 2 then
		pss := 4;
		for ss in [3..s] do
			m := pss;
			pss *:= 2;
			Zeta := Exp(m2PII/pss);
			ZetasNpss := [1,Zeta];
			for k in [2..m] do
				Append(~ZetasNpss,ZetasNpss[k]*Zeta);
			end for;
			ZNP[p][ss] := ZetasNpss;
		end for;	
		else
		pss *:= p;
		Zeta := Exp(m2PII/pss);
		ZetasNpss := [1,Zeta];
		if UBS[p] and s eq 1 then
			m := pm1;
		else
			m := pm1^2;
		end if;
		for k in [2..m] do
			Append(~ZetasNpss,ZetasNpss[k]*Zeta);
		end for;
		if UBS[p] then
			ZetaSqrt := Sqrt(Zeta);
			ZetasNpSq := [ 1, ZetaSqrt ];
			for k in [2..pm1] do
				Append(~ZetasNpSq,ZetasNpSq[k]*ZetasNpss[k]*ZetaSqrt);
			end for;
			ZNP[p+1] := [ ZetasNpSq ];
		end if;
		ZNP[p][1] := ZetasNpss;
		for ss in [2..s] do
			m := pss-1;
			pss *:= p;
			Zeta := Exp(m2PII/pss);
			ZetasNpss := [1,Zeta];
			m *:= pm1;
			for k in [2..m] do
				Append(~ZetasNpss,ZetasNpss[k]*Zeta);
			end for;
			ZNP[p][ss] := ZetasNpss;
		end for;
		end if;
	end procedure;
	t := Cputime();
	if NPO2 gt 0 then
		ComputeZetas(~ZetasNPrimes,2,NPO2);
	end if;
	if PO2 ne 0 then
		l := 2;
	else
		l := 1;
	end if;
	for k in [l..NNF] do
		ComputeZetas(~ZetasNPrimes,NFac[k][1],NFac[k][2]);
	end for;
	vprint RS,2 : "Computing Zetas...",Cputime()-t;

	/* Multiply integers */
	MultTable := [];
	mp := NFac[NNF][1];
	if mp ne 2 then
		pms := Max([NFac[k][1]^NFac[k][2] :k in [1..NNF]]); 
		for j in [1..mp] do
			MultTable[j] := [ j*k+1: k in [1..pms]];
		end for;
	end if;

	function PPFFT(x,p,s)
	/* FFT for prime powers */
		if p eq 2 then
			if s gt 2 then
				X_res := [];
				sm1 := s-1;
				Np := 2^sm1;
				X1 := PPFFT([ x[2*k-1] : k in [1..Np]],2,sm1);
				X2 := PPFFT([ x[2*k] : k in [1..Np]],2,sm1);
				for k in [1..Np] do
					Val := ZetasNPrimes[2][s][k] * X2[k];
					X_res[k] := X1[k] + Val;
					X_res[Np+k] := X1[k] - Val;
				end for;
				return X_res;
			elif s eq 2 then
				x1m3 := x[1]-x[3];x1p3 := x[1]+x[3];
				x2p4 := x[2]+x[4];x2m4 := x[2]-x[4];
				return [ x1p3+x2p4 , x1m3-I*x2m4, x1p3-x2p4, x1m3+I*x2m4 ];
			else
				return [ x[1]+x[2], x[1]-x[2] ];
			end if;		
		else
			X_res := [];
			pm1 := p-1;
			if s eq 1 and UBS[p] then
				vprint RS,2 : "Using Bluestein's algorithm...";
				/* Bluestein's algorithm */
				Zetas_2p := ZetasNPrimes[p+1][1];
				p2m1 := 2*p-1;
				M := Ceiling(Log(2,p))+1;
				MP2 := 2^M; 
				A := [ x[k]*Zetas_2p[k] : k in [1..p] ] cat [ 0 : j in [1..MP2-p] ];
				B := [];
				for k in [2..p] do
					Append(~B,1/Zetas_2p[k]);
				end for;
				B := [1] cat B cat [ 0 : j in [1..MP2-p2m1] ] cat Reverse(B);
				/* Compute convolution of A and B using prime power p=2 FFT's */
				A_FFT := PPFFT(A,2,M); B_FFT := PPFFT(B,2,M);
				/* Multiply and prepare for inverse FFT */
				AB_FFT := PPFFT([ Conjugate(A_FFT[k] * B_FFT[k]) : k in [1..MP2] ],2,M);
				CC := [ (1/MP2) * Conjugate(c) : c in AB_FFT ];
				X_res := [ Zetas_2p[k] * CC[k] : k in [1..p] ];
				return X_res;
			end if;
			Zetas_p := ZetasNPrimes[p][1];
			if s eq 1 then
				X_res := [ x[1] : j in [1..p] ];
				X_res[1] := &+x;
				for k in [1..pm1] do
					X_res[k+1] +:= &+[ Zetas_p[MultTable[j][k]] * x[j+1] : j in [1..pm1]];
				end for;
				return X_res;
			else			
				sm1 := s-1;
				Np := p^sm1;
				Npm1 := Np-1;
				/* List of p sub-FFTs of length p^(s-1) */
				X := [ PPFFT([ x[p*k+l] : k in [0..Npm1]],p,sm1) : l in [1..p] ];
				Zetas_ps := ZetasNPrimes[p][s];
				kjprods := [ Zetas_ps[1] * X[j][1] : j in [2..p] ];
				X_res[1] := X[1][1] + &+[ kjprods[j] * Zetas_p[1] : j in [1..pm1] ];
				for l in [1..pm1] do
					X_res[MultTable[l][Np]] := X[1][1] + &+[ kjprods[j] * Zetas_p[MultTable[j][l]] : j in [1..pm1] ];
				end for;
				for k in [2..Np] do
					km1 := k-1;
					kjprods := [ Zetas_ps[MultTable[j][km1]] * X[j+1][k] : j in [1..pm1] ];
					X_res[k] := X[1][k] + &+[ kjprods[j] * Zetas_p[1] : j in [1..pm1] ];
					for l in [1..pm1] do
						X_res[MultTable[l][Np]+km1] := X[1][k] + &+[ kjprods[j] * Zetas_p[MultTable[j][l]] : j in [1..pm1] ];
					end for;
				end for;
				return X_res;
			end if;
		end if;
	end function;
	
	function CPFFT(x,N1Fac,N2Fac)
		/* Comprime FFT, assumes N1 prime power */
		N1 := N1Fac[1]^N1Fac[2];
		N2 := &*[ N2Fac[k][1]^N2Fac[k][2] : k in [1..#N2Fac] ]; 
		N1N2 := N1*N2;
		N1m1 := N1-1;
		N2m1 := N2-1;

		/* N1 inner FFTs of size N2 */
		X_N2 := [];
		if #N2Fac eq 1 then
			/* Use prime power algorithm */
			for n1 in [0..N1m1] do
				X_N2[n1+1] := PPFFT([x[(n1*N2+n2*N1) mod N1N2 + 1] : n2 in [0..N2m1]],N2Fac[1][1],N2Fac[1][2]);
			end for;
		else	
			/* Recursive call */
			for n1 in [0..N1m1] do
				X_N2[n1+1] := CPFFT([ x[(n1*N2+n2*N1) mod N1N2 + 1] : n2 in [0..N2m1]],<N2Fac[1][1],N2Fac[1][2]>,N2Fac[2..#N2Fac]);
			end for;
		end if;

		/* N2 outer FFTs of size N1 */
		X_N1 := [];
		for n2 in [1..N2] do
			X_N1[n2] := PPFFT([X_N2[n1][n2] : n1 in [1..N1]],N1Fac[1],N1Fac[2]);
		end for;

		/* Inverses */
		N1I := InverseMod(N1,N2); N1IN1 := N1I*N1;
		N2I := InverseMod(N2,N1); N2IN2 := N2I*N2;

		X_res := [ C | ];
		/* N2 outer FFTs of size N1 */
		for k1 in [1..N1m1] do
			X_res[(k1*N2IN2) mod N1N2] := X_N1[1][k1+1];
		end for;
		for k1 in [0..N1m1] do
			k1p1 := k1+1;
			for k2 in [1..N2m1] do
				X_res[(k1*N2IN2+k2*N1IN1) mod N1N2] := X_N1[k2+1][k1p1];
			end for;
		end for;
		Insert(~X_res,1,X_N1[1][1]);
		return X_res;
	end function;

	/* Perform actual FFT (highly recursive!) */
	if NNF eq 1 then
		return PPFFT(X,NFac[1][1],NFac[1][2]);
	else
		return CPFFT(X,NFac[1],NFac[2..NNF]);
	end if;
end intrinsic;



intrinsic ClenshawCurtisIntegrationPoints(N::RngIntElt, Prec::RngIntElt) -> SeqEnum[FldReElt], SeqEnum[FldReElt]
{ Compute the Clenshaw-Curtis integration scheme on N+1 points via Fast-Fourier-Transform. }
	C<I> := ComplexField(Prec);
	m2PII := -2*Pi(C)*I;
	assert N gt 1;

	/* Compute weights via FFT */
	FN2 := Floor(N/2);
	v1 := [2/1];
	if N mod 2 eq 0 then
		v1[FN2+1] := -2/(2*FN2-1);
	else
		v1[FN2+1] := -1/(2*FN2-1);
		v1[FN2+2] := v1[FN2+1];
	end if;
	for k in [2..FN2] do
		v1[k] := -2/((2*k-1)*(2*k-3));
		v1[N-k+2] := v1[k];
	end for;	 
	v0 := [ -1 : j in [1..N] ]; 
	v0[1+FN2] +:= N; 
	v0[1+N-FN2] +:= N;
	v2 := [ v0[k]/(N^2+1+(N mod 2)) : k in [1..N] ];
	v := [ v1[k] + v2[k] : k in [1..N] ];

	/* Perform inverse FFT */
	Y := DiscreteFourierTransform(ChangeUniverse(v,C));
	NInv := Real(C!(1/N));
	Weights := [ NInv * Real(y) : y in Y ];
	Append(~Weights,Weights[1]);	

	/* Compute Abscissas */
	Abscissas := [ Real(One(C)), Cos(Real(Pi(C))*NInv) ];
	for k in [2..Floor(N/2)] do
		Append(~Abscissas,2*Abscissas[2] * Abscissas[k] - Abscissas[k-1]);
	end for;

	if N mod 2 eq 1 then
		Abscissas := [ -x : x in Abscissas ] cat Reverse(Abscissas);
	else
		Abscissas := [ -x : x in Prune(Abscissas) ] cat Reverse(Abscissas);
	end if;
	return Abscissas,Weights;
end intrinsic;

procedure HeuristicBound( Gamma, DFF_Factors, Lr, X )
/* Computes a heuristic bound that for integrating DFF along Gamma */
	C<I> := BaseRing(Universe(DFF_Factors));
	Cz<z> := PolynomialRing(C);
	//m := X`Degree[1];
	m := Degree(X`AffineModel,2);
	q := #Lr;
	if #Gamma`Bounds eq 0 then
		Gamma`IN := Max( [ p : p in [1..q] | Gamma`IntPar gt Lr[p] ] cat [1] );
		assert assigned Gamma`WP;
		if Gamma`IntMethod eq "DE" then
			uj, duj := DistanceToBurger(Gamma`WP,Lr[Gamma`IN]);
			for tj in [-1,1,uj] do
				xj, dxj := Gamma`Evaluate(tj);
				yj := ModifiedFiber(X`ComplexDefPol,xj);
				OneMat := X`DFFEvaluate(DFF_Factors,xj,yj,m);
				OneMat *:= dxj;
				Append(~Gamma`Bounds,10*Max([Abs(c) : c in Eltseq(OneMat)]));	
			end for;
		else
			uj, duj := DistanceToEllipse(Gamma`WP,Lr[Gamma`IN]);
			xj, dxj := Gamma`Evaluate(uj);
			yj := ModifiedFiber(X`ComplexDefPol,xj);
			OneMat := X`DFFEvaluate(DFF_Factors,xj,yj,m);
			OneMat *:= dxj;
			Append(~Gamma`Bounds,10*Max([Abs(c) : c in Eltseq(OneMat)]));
		end if;
	else
		Gamma`IN := q;
	end if;
end procedure;

/*******************************************************************************

	Numerical integration for superelliptic Riemann surfaces
 
	Christian Neurohr, August 2018

*******************************************************************************/

////////////////////////////////////////////////
///  *****  Gauss-Jacobi integration   ***** ///
////////////////////////////////////////////////

/* Error bound for Gauss-Jacobi integration */
function GaussJacobiParameters(P,AB,Prec)
	R := RealField(10);
	D := Log(R!10) * Prec;
	M_r := R!P[1]; r := R!P[2];
	achr := Argcosh(r);
	ChangeUniverse(~AB,R);
	if AB eq [-1/2,-1/2] then
		/* Gauss-Chebyshev */
		N := Ceiling((D+Log(2*Pi(R)*M_r)+1)/(2*achr));
	else
		/* Gauss-Jacobi */
		I1 := 2^(&+AB+1)*Gamma(AB[1]+1)*Gamma(AB[2]+1)/Gamma(&+AB+2);
		c1 := 4*I1*M_r;
		if AB[1] eq AB[2] then
			epow := -2;
		else
			epow := -1;
		end if;
		N := Ceiling((Log(c1)+D-Log(1-Exp(achr)^epow))/(2*achr));
	end if;
	return N;
end function;

intrinsic GaussJacobiIntegrationPoints( AB::SeqEnum[FldRatElt], N::RngIntElt, Prec::RngIntElt ) -> SeqEnum[FldReElt], SeqEnum[FldReElt]
{ REC algorithm for the computation of the Gauss-Jacobi integration scheme }
	
	assert &and[ AB[1] gt -1, AB[2] gt -1];

	// Careful: AB[1] corresponds to (1-u) and AB[2] to (1+u)
	//Reverse(~AB);
	Abscissas := []; Weights := [];
	R := RealField(Prec+5);

	if AB[1] eq AB[2] then
		n := Floor((N+1)/2);
	else
		n := N;
	end if;

	// Gauss-Chebyshev
	if AB eq [-1/2,-1/2] then
		const := 1/(2*N)*Pi(R);
		for k in [1..n] do
			Append(~Abscissas,Cos((2*k-1)*const));
		end for;
		Append(~Weights,2*const);
		return Abscissas,Weights;
	end if;

	// From here on: Gauss-Jacobi

	// Precomputations
	Err := 10^-(Prec+1);
	RN := R!N; N2 := N^2;	
	B := []; C := [];
	APB := R!(AB[1]+AB[2]);
	AMB := R!(AB[1]-AB[2]);
	NAB := R!(2*(N+AB[1])*(N+AB[2]));
	ASQMBSQ := AB[1]^2 - AB[2]^2;
	for j in [1..N] do
		tmp := 2*j + APB;
		tmp2 := 1/(2*j*(j+APB)*(tmp-2));
		Append(~B,[tmp*(tmp-1)*(tmp-2)*tmp2,(tmp-1)*ASQMBSQ*tmp2]);
		Append(~C,2*(j-1+AB[1])*(j-1+AB[2])*tmp*tmp2);
	end for;
	//ChangeUniverse(~A,R);
	OH := R!(1/2);
	AMBOT := AMB * OH;
	APBP2OT := (APB+2) * OH;
	NAMB := N*AMB;
	Ntmp := N*tmp;
	Const := tmp*2^APB*Gamma(AB[1]+RN)*Gamma(AB[2]+RN)/(Gamma(RN+1)*Gamma(RN+APB+1));

	print "B:",B;
	print "C:",C;

	// Start with low precision
	sp := 16;
	RL := RealField(sp);
	
	for k in [1..n] do
		if k eq 1 then
			an := AB[1]/N;
			bn := AB[2]/N;
			r1 := (1+AB[1])*((139/50)/(4+N2) + (98/125)*an/N);
			r2 := 1+(37/25)*an+(24/25)*bn+(113/250)*an^2+(83/100)*an*bn;
			z := 1-r1/r2;
		elif k eq 2 then
			r1 := (41/10+AB[1])/((1+AB[1])*(1+(39/250)*AB[1]));
			r2 := 1+3/50*(N-8)*(1+3/25*AB[1])/N;
			r3 := 1+3/250*AB[2]*(1+(1/4)*Abs(AB[1]))/N;
			z -:= (1-z)*r1*r2*r3;
		elif k eq 3 then
			r1 := (1.67+7/25*AB[1])/(1+37/100*AB[1]);
			r2 := 1+11/50*(N-8)/N;
			r3 := 1+8*AB[2]/((157/25+AB[2])*N2);
			z -:= (Abscissas[1]-z)*r1*r2*r3;
		elif k eq N-1 then
			r1 := (1+47/200*AB[2])/(383/500+119/1000*AB[2]);
			r2 := 1/(1+639/1000*(N-4)/(1+71/100*(N-4)));
			r3 := 1/(1+20*AB[1]/((15/2+AB[1])*N2));
			z +:= (z-Abscissas[N-3])*r1*r2*r3;
		elif k eq N then
			r1 := (1+37/100*AB[2])/(167/100+7/25*AB[2]);
			r2 := 1/(1+11/50*(N-8)/N);
			r3 := 1/(1+8*AB[1]/((157/25+AB[1])*N2));
			z +:= (z-Abscissas[N-2])*r1*r2*r3;
		else
			z := 3*Abscissas[k-1]-3*Abscissas[k-2]+Abscissas[k-3];
		end if;
		z := RL!z;
		p := sp;
    		repeat
			p := Min(2*p,Prec);
			z := ChangePrecision(z,p);
			p1 := AMBOT+APBP2OT*z;
			p2 := 1;
			for j in [2..N] do
				p3 := p2;
				p2 := p1;
				p1 := (B[j][1]*z + B[j][2])*p2-C[j]*p3;
			end for;
			ppinv := tmp*(1-z*z)/((NAMB-Ntmp*z)*p1+NAB*p2);
      			fxk := p1*ppinv; 
			z -:= fxk;
		until Abs(fxk) lt Err;
		Abscissas[k] := z;
		Weights[k] := Const*ppinv/p2;
    	end for;
	return Abscissas,Weights;
end intrinsic;

/* Construct the Gauss-Jacobi integration scheme */
procedure SE_GJ_Integration( Params, X : AJM := false )
	/* Parameters = < M_i, r_i > where N_i < N_{i+1} */
	m := X`Degree[1]; 
	Prec := Precision(X`ComplexFields[2]);
	DFF := X`HolomorphicDifferentials;
	ALLGJ_Integrations := [];
	if AJM then
		NSchemes := #X`IntSchemes["GJ"]; 
		if NSchemes eq 0 or X`IntSchemes["GJ"][1][1]`Prec lt Precision(X`ComplexFields[3]) then 
			for P in Params do
				GJ_Integrations := [];
				N := GaussJacobiParameters(P,[0/1,-(m-1)/m],Prec);
				for j in [DFF[1]..m-1] do
					GJInt := New(IntScheme);
					GJInt`Type := "GJ";
					GJInt`AlphaBeta := [0/1,-j/m];
					GJInt`N := N;
					GJInt`Params := P;
					GJInt`Abscissas, GJInt`Weights := GaussJacobiIntegrationPoints(GJInt`N,Precision(X`ComplexFields[3]),0,-j/m);
					GJInt`Prec := Precision(X`ComplexFields[3]);
					Append(~GJ_Integrations,GJInt);
				end for;
				Append(~ALLGJ_Integrations,GJ_Integrations);
			end for;
			X`IntSchemes["GJ"] := ALLGJ_Integrations;
		else
			Ns := [ IntSch[1]`N : IntSch in X`IntSchemes["GJ"] ];
			for k in [1..#Params] do
				GJ_Integrations := [];
				N := GaussJacobiParameters(Params[k],[0/1,-(m-1)/m],Prec);
				if N gt Ns[1] then
					for j in [DFF[1]..m-1] do
						GJInt := New(IntScheme);
						GJInt`Type := "GJ";
						GJInt`AlphaBeta := [0/1,-j/m];
						GJInt`N := N;
						GJInt`Params := Params[k];
						GJInt`Abscissas, GJInt`Weights := GaussJacobiIntegrationPoints(GJInt`N,Precision(X`ComplexFields[3]),0,-j/m);
						GJInt`Prec := Precision(X`ComplexFields[3]);
						Append(~GJ_Integrations,GJInt);
					end for;
					Append(~ALLGJ_Integrations,GJ_Integrations);
					Ns[1] := N;
				else
					l := Max( [ j : j in [1..NSchemes] | Ns[j] ge N ] );
					Append(~ALLGJ_Integrations,X`IntSchemes["GJ"][l]);
				end if;
			end for;
			X`IntSchemes["GJ"] := ALLGJ_Integrations;
		end if;
	else
		for P in Params do
			GJ_Integrations := [];
			N := GaussJacobiParameters(P,[-(m-1)/m,-(m-1)/m],Prec);
			for j in [DFF[1]..m-1] do
				GJInt := New(IntScheme);
				GJInt`Type := "GJ";
				GJInt`AlphaBeta := [-j/m,-j/m];
				GJInt`N := N;
				GJInt`Params := P;
				GJInt`Abscissas, GJInt`Weights := GaussJacobiIntegrationPoints(GJInt`N,Precision(X`ComplexFields[3]),-j/m,-j/m);
				GJInt`Prec := Precision(X`ComplexFields[3]);
				Append(~GJ_Integrations,GJInt);
			end for;
			Append(~X`IntSchemes["GJ"],GJ_Integrations);
		end for;
	end if;
end procedure;


///////////////////////////////////////////////////////////////
///        ***** Double-exponential integration *****       ///
///////////////////////////////////////////////////////////////

RPI := Pi(RealField(30));

function Distance_1(P)
	xP := Abs(Re(P));
	if xP gt 1 then
		return Abs(xP-1+Parent(P).1*Im(P));
	else
		return Abs(Im(P));
	end if;
end function;

function Bound_M1(CCV,len,m : AJM := false)
/* Compute M_1 for double-exponential integration */
	M1 := (1/&*[ Distance_1(CCV[k]) : k in [1..len] ])^(1/m);
	if AJM then
		M1 *:= 2^(1/m);
	end if;
	if M1 gt 1 then
		return M1^(m-1);
	else
		return M1;
	end if;
end function;

function Bound_M2(CCV,len,m,n,r : Lambda := RPI/2, AJM := false )
/* Compute an approximation to M_2 for double-exponential integration */
	/* Complex field */
	C := Universe(CCV);

	/* Search on interval [0,t_max] */
	tmax := Argcosh(RPI/(2*Lambda*Sin(r)));

	Phi := function(t)
		return Tanh(Lambda*Sinh(t+C.1*r));
	end function;
	Dist := function(z,P)
		return Abs(z-Abs(Re(P)) + C.1*Abs(Im(P)));
	end function;

	/* Number of evaluations */
	ss := 20;

	/* Abs(1-tanh(sinh(I*r))) */
	MDTO := Abs(1-Phi(0));

	M2 := 1;
	for k in [0..ss] do
		t := k/ss*tmax;
		z := Phi(t);
		za := Abs(z);
		if za gt 1 then
			km := za^(n-2);
		else
			km := za;
		end if;
		if AJM then
			u := (MDTO/&*[ Dist(z,CCV[l]): l in [1..len] ])^(1/m);
		else
			u := (1/&*[ Dist(z,CCV[l]): l in [1..len] ])^(1/m);
		end if;
		if u gt 1 then
			u := u^(m-1);
		end if;
		km *:= u;
		if km gt M2 then
			xm := t;
		end if;
		M2 := Max(km,M2);
	end for;
	return M2;
end function;

/* Analytic continuation for superelliptic Riemann surfaces */
function ImSgn(z)
	if IsReal(z) then
		return 1;
	else
		return Sign(Im(z));
	end if;
end function;

function AC_mthRoot(x,E,Zetas,m,n)
/* Used for analytic continuation of y = f(x)^(1/m) */
	WindingNr := 0;
	if 1 le E`up then
		z := E`Data[1]-x;
	else
		z := x-E`Data[1];
	end if;
	isgnz := E`Isgn[1];
	for k in [2..n] do
		if k le E`up then
			z *:= E`Data[k]-x;
		else
			z *:= x-E`Data[k];
		end if;
		if isgnz eq E`Isgn[k] then
			isgnz := ImSgn(z);
			if isgnz ne E`Isgn[k] then
				if E`Isgn[k] eq 1 then
					WindingNr +:= 2;
				else
					WindingNr -:= 2;
				end if;
			end if;
		else
			isgnz := ImSgn(z);
		end if;
	end for;
	if Im(z) eq 0 and Re(z) lt 0 then
		z := -z;
		WindingNr +:= 1;	
	end if;
	if m eq 2 then
		return Zetas[WindingNr mod 4 + 1]  * Sqrt(z);
	else
		return Zetas[WindingNr mod (2*m) + 1]  * Exp(Log(z)/m);
	end if;
end function;

/* Construct the double exponential integration scheme */
procedure SE_DE_Integration( Params,X : AJM := false )
	/* Parameters = < M1,M2,[ r_min,..,r_max ] > where r_i < r_{i+1} */
	X`IntSchemes["DE"] := [];
	m := X`Degree[1];
	DFF := X`HolomorphicDifferentials;
	R := RealField(Precision(X`ComplexFields[3]));
	RL := RealField(10);

	/* Worst Alpha */
	Alpha := 1/m;

	/* Compute D */
	D := Precision(X`ComplexFields[2]) * Log(RL!10);

	for P in Params do
		r := RL!P[3];
		/* Compute parameters N,h for DE integration */
		X_r := Cos(r) * Sqrt(1/Sin(r) - 1);
		B_ra := (2/Cos(r)) * ( (X_r/2) * (1/(Cos(Pi(RL)/2*Sin(r))^(2*Alpha)) + (1/X_r^(2*Alpha))) ) + (1/(2*Alpha*Sinh(X_r)^(2*Alpha)));
		h := (2 * Pi(RL) * r)/( D+Log(2*P[2] * B_ra + 1));
		N := Ceiling(Argsinh((D+ Log((2^(2*Alpha+1)*P[1])/Alpha )) / ( Alpha*Pi(RL) ))/h);
		/* Create new integration scheme */
		DE_Int := New(IntScheme);
		DE_Int`N := N;
		DE_Int`Type := "DE";
		DE_Int`Bounds := [ P[1],P[2] ];
		DE_Int`Prec := Precision(R); 
		DE_Int`IntPar := r;
		/* Compute abscissas and weights */
		DE_Int`Abscissas, DE_Int`Weights, DE_Int`ExtraWeights := TanhSinhIntegrationPoints(N,R!h);
		if AJM then
			DE_Int`ExtraWeights := [ ((1-DE_Int`Abscissas[k])*DE_Int`ExtraWeights[k])^Alpha : k in [1..2*N+1] ];
		else
			DE_Int`ExtraWeights := [ w^Alpha : w in DE_Int`ExtraWeights ];
		end if;
		Append(~X`IntSchemes["DE"],DE_Int);
	end for;
end procedure;


/* Constant factors for superelliptic integrals */
function SE_Integrals_Factor( VectorIntegral, Edge, X )
	m := X`Degree[1];
	n := X`Degree[2];
	DFF := X`HolomorphicDifferentials;
	ElementaryIntegrals := []; // Required for Abel-Jacobi map
	Integrals := []; // g x (m-1) array of integrals

	/* ((b-a)/2)^i, i = 1,..,n */
	Fact1 := [ Edge`Data[n-1] ];
	for j in [2..DFF[3][DFF[2]]+1] do
		Append(~Fact1,Edge`Data[n-1] * Fact1[j-1]);
	end for;
	/* (2/(b-a))^(nj/m), j = 1,..,m-1 */
	z := Exp( (n/m) * -Log(Edge`Data[n-1]) ); Fact2 := [z];
	for j in [2..DFF[2]+DFF[1]-1] do
		Append(~Fact2,z*Fact2[j-1]);
	end for;

	/* Shift integral back by powers of (p+a)/(p-a) */
	ct := 0;
	for j in [1..DFF[2]] do
		PolynomialShiftVector(~VectorIntegral,Edge`Data[n],DFF[3][j],ct);
		ct +:= DFF[3][j];
	end for;

	/* Multiply by correct power of zeta, (1-zeta) and ((p-a)/2)^(i+1-jn/m) */
	ct := 1; 
	for j in [1..DFF[2]] do
		DFF3jm1 := DFF[3][j]-1;
		for ij in [0..DFF3jm1] do
			Pow := -((Edge`up + 1) mod 2)*DFF[4][ct] mod (2*m) + 1;
			VectorIntegral[ct] *:= X`DifferentialChangeMatrix[ct] * X`Zetas[Pow] * Fact1[ij+1] * Fact2[DFF[4][ct]];
			Append(~ElementaryIntegrals, VectorIntegral[ct]);
			Pow := -2*DFF[4][ct] mod (2*m) + 1;
			VectorIntegral[ct] *:= (1 - X`Zetas[Pow]);
			NextIntegrals := [ VectorIntegral[ct] ];
			for l in [1..m-2] do
				Pow := -2*l*DFF[4][ct] mod (2*m) + 1;
				Append(~NextIntegrals,X`Zetas[Pow]*VectorIntegral[ct]);
			end for; 
			Append(~Integrals,NextIntegrals);
			ct +:= 1;
		end for;
	end for;
	return Integrals, ElementaryIntegrals;
end function;
function SE_Integrals_Factor_AJM( VectorIntegral,Edge,X)
/* EdgeData = [ u_1 , ... , u_{n-1}, (p_x-a)/2, (p_x+a)/(p_x-a) */
	C<I> := X`ComplexFields[3]; 
	g := X`Genus; 
	m := X`Degree[1];
	n := X`Degree[2];
	DFF := X`HolomorphicDifferentials;

	/* ((p-a)/2)^i, i = 1,..,max_i+1 */
	Fact1 := [ Edge`Data[n] ]; k := DFF[3][DFF[2]]+1;
	for j in [2..k] do
		Append(~Fact1,Edge`Data[n] * Fact1[j-1]);
	end for;
	/* (2/(p-a))^(nj/m), j = 1,..,m-1 */
	z := Exp( (n/m) * -Log(Edge`Data[n]) ); Fact2 := [z]; k := DFF[2]+DFF[1]-1;
	for j in [2..k] do
		Append(~Fact2,z*Fact2[j-1]);
	end for;

	/* Shift integral back by powers of (p+a)/(p-a) */
	ct := 0;
	for j in [1..DFF[2]] do
		PolynomialShiftVector(~VectorIntegral,Edge`Data[n+1],DFF[3][j],ct);
		ct +:= DFF[3][j];
	end for;

	/* Correct sheet? */
	P_y_AC := Exp( (n/m) * Log(2*Edge`Data[n]) + (1/m) * Log(X`LeadingCoeff))  * X`Zetas[Edge`up mod (2*m) + 1]  / AC_mthRoot(One(C),Edge,X`Zetas,m,n-1); 

	/* Shifting number at P_y */
	s := Round((m/(2*Real(Pi(C)))) * ( Arg(Edge`EP[2][2]) - Arg(P_y_AC) ));
	
	/* Multiply by correct power of zeta and ((p-a)/2)^(i+1-jn/m) */
	ct := 1;
	for j in [1..DFF[2]] do
		DFF3jm1 := DFF[3][j]-1;
		for ij in [0..DFF3jm1] do
			Pow := -(Edge`up + 2*s)*DFF[4][ct] mod (2*m) + 1;
			VectorIntegral[ct] *:= X`DifferentialChangeMatrix[ct] * X`Zetas[Pow] * Fact1[ij+1] * Fact2[DFF[4][ct]];
			ct +:= 1;
		end for;
	end for;

	return VectorIntegral;
end function;
/* Compute superelliptic integrals for spanning tree */
function DE_Integral(Edge,X)
	C_0 := Zero(X`ComplexFields[3]); 
	m := X`Degree[1]; 
	nm2 := X`Degree[2]-2;
	DFF := X`HolomorphicDifferentials;
	DEInt := X`IntSchemes[Edge`IntSch];
	VectorIntegral := [ C_0 : j in [1..X`Genus] ];

	// Start with zero
	y := DEInt`Weights[1][2]/AC_mthRoot(0,Edge,X`Zetas,m,nm2); // 1/y(0)
	wy := y^DFF[1] * DEInt`Weights[1][1];
	ct := 1;
	for j in [1..DFF[2]] do
		if j gt 1 then
			wy *:= y;
		end if;
		wyx := wy;
		VectorIntegral[ct] +:= wyx;
		ct +:= DFF[3][j];
	end for;

	// Evaluate differentials at abisccsas
	for t in [2..DEInt`NPoints] do
		x := DEInt`Abscissas[t];
		mx := -x;
		y1 := DEInt`Weights[t][2]/AC_mthRoot(x,Edge,X`Zetas,m,nm2); // 1/y(x)
		y2 := DEInt`Weights[t][2]/AC_mthRoot(mx,Edge,X`Zetas,m,nm2); // 1/y(-x)
		wy1 := y1^DFF[1] * DEInt`Weights[t][1];
		wy2 := y2^DFF[1] * DEInt`Weights[t][1];
		ct := 1;
		for j in [1..DFF[2]] do
			if j gt 1 then
				wy1 *:= y1;
				wy2 *:= y2;
			end if;
			wyx1 := wy1;
			wyx2 := wy2;
			VectorIntegral[ct] +:= wyx1 + wyx2;
			ct +:= 1;
			for k in [1..DFF[3][j]-1] do
				wyx1 *:= x;
				wyx2 *:= mx;
				VectorIntegral[ct] +:= wyx1 + wyx2;
				ct +:= 1;
			end for;
		end for;
	end for;
	for j in [1..X`Genus] do
		VectorIntegral[j] *:= DEInt`Factor;
	end for;
	return VectorIntegral;
end function;
function GJ_Integral(Edge,X)
	C_0 := Zero(X`ComplexFields[3]); 
	GJInts := X`IntSchemes[Edge`IntSch];
	N := GJInts[1]`NPoints;
	DFF := X`HolomorphicDifferentials;
	VectorIntegral := [ C_0 : j in [1..X`Genus] ];
	N2 := Floor(N/2);
	
	if N mod 2 eq 1 then
		ct := 1;
		y := 1/AC_mthRoot(0,Edge,X`Zetas,X`Degree[1],X`Degree[2]-2); // 1/y(0)
		for j in [1..DFF[2]] do
			wy := GJInts[j]`Weights[N2+1] * y^(DFF[4][ct]);
			VectorIntegral[ct] +:= wy;
			ct +:= DFF[3][j];
		end for;
	end if;

	// Evaluate differentials at abisccsas
	for t in [1..N2] do
		ct := 1;
		for j in [1..DFF[2]] do
			x := GJInts[j]`Abscissas[t];
			mx := -x;
			y1 := 1/AC_mthRoot(x,Edge,X`Zetas,X`Degree[1],X`Degree[2]-2); // 1/y(x)
			y2 := 1/AC_mthRoot(mx,Edge,X`Zetas,X`Degree[1],X`Degree[2]-2); // 1/y(-x)
			wy1 := GJInts[j]`Weights[t] * y1^(DFF[4][ct]);
			wy2 := GJInts[j]`Weights[t] * y2^(DFF[4][ct]);
			VectorIntegral[ct] +:= wy1 + wy2;
			ct +:= 1;
			for k in [1..DFF[3][j]-1] do
				wy1 *:= x;
				wy2 *:= mx;
				VectorIntegral[ct] +:= wy1 + wy2;
				ct +:= 1;
			end for;
		end for;
	end for;
	return VectorIntegral;
end function;
function SE_Integrals_Tree(X)
	Periods := []; ElementaryIntegrals := [];
	for k in [1..X`Degree[2]-1] do
		E := X`SpanningTree`Edges[k];
		vprint RS,2 : "Integrating edge #:",k;
		if E`IntMethod eq "DE" then
			DEInt := X`IntSchemes["DE"][E`IntSch];
			VectorIntegral := DE_Integral(E,X);
		else
			GJInts := X`IntSchemes["GJ"][E`IntSch];
			GJAbscissas := [ GJInt`Abscissas : GJInt in GJInts ];
			GJWeights := [ GJInt`Weights : GJInt in GJInts ];
			VectorIntegral := GJ_Integral(E,X);
		end if;
		P, EI := SE_Integrals_Factor(VectorIntegral,E,X);
		Append(~Periods,P); Append(~ElementaryIntegrals,EI);
	end for;
	return Periods, ElementaryIntegrals;
end function;

/* Compute superelliptic integrals for Abel-Jacobi map */
function SE_Integrals_Edge_AJM(E,X)
	if E`IntMethod eq "DE" then
		DEInt := X`IntSchemes["DE"][E`IntSch];
		VectorIntegral := DE_Integral(E,X);
//InternalSEDEIntegration(<2*DEInt`N+1,DEInt`Abscissas,DEInt`Weights,DEInt`ExtraWeights,X`HolomorphicDifferentials,E`Data,E`Isgn,X`Zetas,X`Degree[1],X`Degree[2]-1,E`up,X`Genus>);
	else
		GJInts := X`IntSchemes["GJ"][E`IntSch];
		GJAbscissas := [ GJInt`Abscissas : GJInt in GJInts ];
		GJWeights := [ GJInt`Weights : GJInt in GJInts ];
		VectorIntegral := GJ_Integral(E,X);
//InternalSEGJIntegration(<GJInts[1]`N,GJAbscissas,GJWeights,X`HolomorphicDifferentials,E`Data,E`Isgn,X`Zetas,X`Degree[1],X`Degree[2]-1,E`up,X`Genus>);
	end if;
	return SE_Integrals_Factor_AJM(VectorIntegral,E,X);
end function;


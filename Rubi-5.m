(* ::Package:: *)

(* ::Title:: *)
(*Rubi 5 Integration Rules (prototype)*)


(* ::Section::Closed:: *)
(*0 Generic Rules*)


Clear[Int]


Int[a_,x_Symbol] := a*x /; FreeQ[a,x]


Int[a_*Fx_,x_Symbol] := a \[Star] Int[Fx,x] /; FreeQ[a,x]


(* ::Section::Closed:: *)
(*1 Algebraic Functions*)


(* ::Subsection::Closed:: *)
(*1.0 Monomial*)


Int[(a_./x_)^p_,x_Symbol] :=
  -a*(a/x)^(p-1)/(p-1) /;
FreeQ[{a,p},x] && Not[IntegerQ[p]]


Int[(a_.*x_^n_)^p_,x_Symbol] :=
  (a*x^n)^p/x^(n*p) \[Star] Int111[0,1,n*p,x] /;
FreeQ[{a,n,p},x] && Not[IntegerQ[p]]


(* ::Subsection::Closed:: *)
(*1.1 Linear*)


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.1:  Int[(a+b x)^m, x] \[RightArrow] Int111[a, b, m, x]*)


Int[(a_.+b_.*x_)^m_.,x_Symbol] := Int111[a,b,m,x] /;
  FreeQ[{a,b,m},x]


Int111::usage =
  "Int111[a,b,m,x] returns the antiderivative of (a+b x)^m wrt x.";


Int111[a_,b_,m_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m*x,
  If[EqQ[m,-1],
    Log[a+b*x]/b,
  (a+b*x)^(m+1)/(b*(m+1))]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.2:  Int[(a+b x)^m (c+d x)^n, x] \[RightArrow] Int112[a, b, m, c, d, n, x]*)


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] := Int112[a,b,m,c,d,n,x] /;
  FreeQ[{a,b,m,c,d,n},x]


Int112::usage =
  "Int112[a,b,m,c,d,n,x] returns the antiderivative of (a+b x)^m (c+d x)^n wrt x.";


Int112[a_,b_,m_,c_,d_,n_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m \[Star] Int111[c,d,n,x],
  If[EqQ[n,0] || EqQ[d,0],
    (c+d*x)^n \[Star] Int111[a,b,m,x],
  Defer[Int112][(a+b*x)^m*(c+d*x)^n,x]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.3:  Int[(a+b x)^m (c+d x)^n (e+f x)^p, x] \[RightArrow] Int113[a, b, m, c, d, n, e, f, p, x]*)


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] := Int113[a,b,m,c,d,n,e,f,p,x] /;
  FreeQ[{a,b,m,c,d,n,e,f,p},x]


Int113::usage =
  "Int113[a,b,m,c,d,n,e,f,p,x] returns the antiderivative of (a+b x)^m (c+d x)^n (e+f x)^p wrt x.";


Int113[a_,b_,m_,c_,d_,n_,e_,f_,p_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m \[Star] Int112[c,d,n,e,f,p,x],
  If[EqQ[n,0] || EqQ[d,0],
    (c+d*x)^n \[Star] Int112[a,b,m,e,f,p,x],
  If[EqQ[p,0] || EqQ[f,0],
    (e+f*x)^p \[Star] Int112[a,b,m,c,d,n,x],
  Defer[Int113][(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.4:  Int[(a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q, x] \[RightArrow] Int114[a, b, m, c, d, n, e, f, p, g, h, q, x]*)
(**)


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] := Int114[a,b,m,c,d,n,e,f,p,g,h,q,x] /;
  FreeQ[{a,b,m,c,d,n,e,f,p,g,h,q},x]


Int114::usage =
  "Int114[a,b,m,c,d,n,e,f,p,g,h,q,x] returns the antiderivative of (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q wrt x.";


Int114[a_,b_,m_,c_,d_,n_,e_,f_,p_,g_,h_,q_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m \[Star] Int113[c,d,n,e,f,p,g,h,q,x],
  If[EqQ[n,0] || EqQ[d,0],
    (c+d*x)^n \[Star] Int113[a,b,m,e,f,p,g,h,q,x],
  If[EqQ[p,0] || EqQ[f,0],
    (e+f*x)^p \[Star] Int113[a,b,m,c,d,n,g,h,q,x],
  If[EqQ[q,0] || EqQ[h,0],
    (g+h*x)^q \[Star] Int113[a,b,m,c,d,n,e,f,p,x],
  Defer[Int114][(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.5:  Int[P[x] (a+b x)^m, x] \[RightArrow] Int115[P[x], a, b, m, x]*)


Int[Px_*(a_.+b_.*x_)^m_.,x_Symbol] := Int115[Px,a,b,m,x] /;
  FreeQ[{a,b,m},x] && PolyQ[Px,x]


Int115::usage =
  "If P[x] is a polynomial in x, Int115[P[x],a,b,m,x] returns the antiderivative of P[x] (a+b x)^m wrt x.";


Int115[Px_,a_,b_,m_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m \[Star] Int[Px,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int111[a,b,m,x],
  If[PolyQ[Px,x,1],
    Int112[a,b,m,Coeff[Px,x,0],Coeff[Px,x,1],1,x],
  If[PolyQ[Px,x,2],
    Int122[a,b,m,Coeff[Px,x,0],Coeff[Px,x,1],Coeff[Px,x,2],1,x],
  Defer[Int115][Px*(a+b*x)^m,x]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.6:  Int[P[x] (a+b x)^m (c+d x)^n, x] \[RightArrow] Int116[P[x], a, b, m, c, d, n, x]*)


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] := Int116[Px,a,b,m,c,d,n,x] /;
  FreeQ[{a,b,m,c,d,n},x] && PolyQ[Px,x]


Int116::usage =
  "If P[x] is a polynomial in x, Int116[P[x],a,b,m,c,d,n,x] returns the antiderivative of P[x] (a+b x)^m (c+d x)^n wrt x.";


Int116[Px_,a_,b_,m_,c_,d_,n_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m \[Star] Int115[Px,c,d,n,x],
  If[EqQ[n,0] || EqQ[d,0],
    (c+d*x)^n \[Star] Int115[Px,a,b,m,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int112[a,b,m,c,d,n,x],
  If[PolyQ[Px,x,1],
    Int113[a,b,m,c,d,n,Coeff[Px,x,0],Coeff[Px,x,1],1,x],
  If[PolyQ[Px,x,2],
    Int123[a,b,m,c,d,n,Coeff[Px,x,0],Coeff[Px,x,1],Coeff[Px,x,2],1,x],
  Defer[Int116][Px*(a+b*x)^m*(c+d*x)^n,x]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.7:  Int[P[x] (a+b x)^m (c+d x)^n (e+f x)^p, x] \[RightArrow] Int117[P[x], a, b, m, c, d, n, e, f, p, x]*)


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] := Int117[Px,a,b,m,c,d,n,e,f,p,x] /;
  FreeQ[{a,b,m,c,d,n,e,f,p},x] && PolyQ[Px,x]


Int117::usage =
  "If P[x] is a polynomial in x, Int117[P[x],a,b,m,c,d,n,e,f,p,x] returns the antiderivative of P[x] (a+b x)^m (c+d x)^n (e+f x)^p wrt x.";


Int117[Px_,a_,b_,m_,c_,d_,n_,e_,f_,p_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m \[Star] Int116[Px,c,d,n,e,f,p,x],
  If[EqQ[n,0] || EqQ[d,0],
    (c+d*x)^n \[Star] Int116[Px,a,b,m,e,f,p,x],
  If[EqQ[p,0] || EqQ[f,0],
    (e+f*x)^p \[Star] Int116[Px,a,b,m,c,d,n,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int113[a,b,m,c,d,n,e,f,p,x],
  If[PolyQ[Px,x,1],
    Int114[a,b,m,c,d,n,e,f,p,Coeff[Px,x,0],Coeff[Px,x,1],1,x],
  Defer[Int117][Px*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.1.8:  Int[P[x] (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q, x] \[RightArrow] Int118[P[x], a, b, m, c, d, n, e, f, p, g, h, q, x]*)


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] := Int118[Px,a,b,m,c,d,n,e,f,p,g,h,q,x] /;
  FreeQ[{a,b,m,c,d,n,e,f,p,g,h,q},x] && PolyQ[Px,x]


Int118::usage =
  "If P[x] is a polynomial in x, Int118[P[x],a,b,m,c,d,n,e,f,p,g,h,q,x] returns the antiderivative of P[x] (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q wrt x.";


Int118[Px_,a_,b_,m_,c_,d_,n_,e_,f_,p_,g_,h_,q_,x_] :=
  If[EqQ[m,0] || EqQ[b,0],
    (a+b*x)^m \[Star] Int117[Px,c,d,n,e,f,p,g,h,q,x],
  If[EqQ[n,0] || EqQ[d,0],
    (c+d*x)^n \[Star] Int117[Px,a,b,m,e,f,p,g,h,q,x],
  If[EqQ[p,0] || EqQ[f,0],
    (e+f*x)^p \[Star] Int117[Px,a,b,m,c,d,n,g,h,q,x],
  If[EqQ[q,0] || EqQ[h,0],
    (g+h*x)^q \[Star] Int117[Px,a,b,m,c,d,n,e,f,p,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int114[a,b,m,c,d,n,e,f,p,g,h,q,x],  
  Defer[Int118][Px*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x]]]]]]]


(* ::Subsection::Closed:: *)
(*1.2 Quadratic*)


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.1:  Int[(a+b x+c x^2)^p, x] \[RightArrow] Int121[a, b, c, p, x]*)


Int[(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] := Int121[a,b,c,p,x] /;
  FreeQ[{a,b,c,p},x]


Int121::usage =
  "Int121[a,b,c,p,x] returns the antiderivative of (a+b x+c x^2)^p wrt x.";


Int121[a_,b_,c_,p_,x_] :=
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p*x,
  If[EqQ[c,0],
    Int111[a,b,p,x],
  If[EqQ[b,0],
    Int151[a,c,p,2,x],
  If[EqQ[b^2-4*a*c,0],
    If[IntegerQ[p],
      (b/2+c*x)^(2*p+1)/(c^(p+1)*(2*p+1)),
    (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p])) \[Star] Int111[b/2,c,2*p,x]],
  If[IntegerQ[p],
    If[EqQ[p,1],
      a*x + b*x^2/2 + c*x^3/3,
    If[EqQ[a,0],
      Int[Apart[x^p*(b+c*x)^p,x],x],
    If[EqQ[p,-1],
      If[NiceSqrtQ[b^2-4*a*c],
        With[{q=Rt[b^2-4*a*c,2]}, 2*c/q \[Star] Int111[b-q,2*c,-1,x] - 2*c/q \[Star] Int111[b+q,2*c,-1,x]],
      With[{q=1-4*Simplify[a*c/b^2]}, If[RationalQ[q] && (EqQ[q^2,1] || Not[RationalQ[b^2-4*a*c]]),
        -2/b \[Star] Subst[Int151[q,-1,-1,2,x],x,1+2*c*x/b],
      -2 \[Star] Subst[Int151[Simplify[b^2-4*a*c],-1,-1,2,x],x,b+2*c*x]]]],
    If[NiceSqrtQ[b^2-4*a*c] && Not[FractionalPowerFactorQ[Rt[b^2-4*a*c,2]]],
      With[{q=Rt[b^2-4*a*c,2]}, 1/c^p \[Star] Int[Apart[(b/2-q/2+c*x)^p*(b/2+q/2+c*x)^p,x],x]],
    If[GtQ[p,0],
      Int[Apart[(a+b*x+c*x^2)^p,x],x],
    (b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 2*c*(2*p+3)/((p+1)*(b^2-4*a*c)) \[Star] Int121[a,b,c,p+1,x]]]]]],
  If[GtQ[p,0] && (IntegerQ[4*p] || IntegerQ[3*p]),
    (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) - p*(b^2-4*a*c)/(2*c*(2*p+1)) \[Star] Int121[a,b,c,p-1,x],
  If[LtQ[p,-1] && (IntegerQ[4*p] || IntegerQ[3*p]),
    If[EqQ[p,-3/2],
      -2*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]),
    (b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 2*c*(2*p+3)/((p+1)*(b^2-4*a*c)) \[Star] Int121[a,b,c,p+1,x]],
  If[EqQ[a,0],
    If[LtQ[b^2/c,0],
      1/(2^(2*p+1)*c*(-c/(b^2))^p) \[Star] Subst[Int151[1,-1/b^2,p,2,x],x,b+2*c*x],
    If[EqQ[p,-1/2],
      2 \[Star] Subst[Int151[1,-c,-1,2,x],x,x/Sqrt[b*x+c*x^2]],
    If[IntegerQ[4*p] || IntegerQ[3*p],
      (b*x+c*x^2)^p/(-c*(b*x+c*x^2)/(b^2))^p \[Star] Int121[0,-c/b,-c^2/b^2,p,x],
    -(b*x+c*x^2)^(p+1)/(b*(p+1)*(-c*x/b)^(p+1))*Hypergeometric2F1[-p,p+1,p+2,1+c*x/b]]]],
  If[LtQ[c/Simplify[b^2-4*a*c],0],
    With[{q=Simplify[b^2-4*a*c]}, 1/(2^(2*p+1)*c*(-c/q)^p) \[Star] Subst[Int151[1,-1/q,p,2,x],x,b+2*c*x]],
  If[EqQ[p,-1/2],
    2 \[Star] Subst[Int151[4*c,-1,-1,2,x],x,(b+2*c*x)/Sqrt[a+b*x+c*x^2]],
  If[IntegerQ[4*p] || IntegerQ[3*p],
    With[{k=Denominator[p]}, k*Sqrt[(b+2*c*x)^2]/(b+2*c*x) \[Star] Subst[Int152[1,k*(p+1)-1,b^2-4*a*c,4*c,-1/2,k,x],x,(a+b*x+c*x^2)^(1/k)]],
  With[{q=Rt[b^2-4*a*c,2]}, -(a+b*x+c*x^2)^(p+1)/(q*(p+1)*((q-b-2*c*x)/(2*q))^(p+1))*Hypergeometric2F1[-p,p+1,p+2,(b+q+2*c*x)/(2*q)]]]]]]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.2:  Int[(d+e x)^m (a+b x+c x^2)^p, x] \[RightArrow] Int122[d, e, m, a, b, c, p, x]*)


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] := Int122[d,e,m,a,b,c,p,x] /;
  FreeQ[{d,e,m,a,b,c,p},x]

Int[(d_.+e_.*x_)^m_.*(a_.+c_.*x_^2)^p_,x_Symbol] := Int122[d,e,m,a,0,c,p,x] /;
  FreeQ[{d,e,m,a,c,p},x]


Int122::usage =
  "Int122[d,e,m,a,b,c,p,x] returns the antiderivative of (d+e x)^m (a+b x+c x^2)^p wrt x.";


Int122[d_,e_,m_,a_,b_,c_,p_,x_] :=
  If[EqQ[m,0] || EqQ[e,0],
    (d+e*x)^m \[Star] Int121[a,b,c,p,x],
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int111[d,e,m,x],
  If[EqQ[c,0],
    Int112[d,e,m,a,b,p,x],
  Defer[Int122][(d+e*x)^m*(a+b*x+c*x^2)^p,x]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.3:  Int[(d+e x)^m (f+g x)^n (a+b x+c x^2)^p, x] \[RightArrow] Int123[d, e, m, f, g, n, a, b, c, p, x]*)


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] := Int123[d,e,m,f,g,n,a,b,c,p,x] /;
  FreeQ[{d,e,m,f,g,n,a,b,c,p},x]

Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+c_.*x_^2)^p_.,x_Symbol] := Int123[d,e,m,f,g,n,a,0,c,p,x] /;
  FreeQ[{d,e,m,f,g,n,a,c,p},x]


Int123::usage =
  "Int123[d,e,m,f,g,n,a,b,c,p,x] returns the antiderivative of (d+e x)^m (f+g x)^n (a+b x+c x^2)^p wrt x.";


Int123[d_,e_,m_,f_,g_,n_,a_,b_,c_,p_,x_] :=
  If[EqQ[m,0] || EqQ[e,0],
    (d+e*x)^m \[Star] Int122[f,g,n,a,b,c,p,x],
  If[EqQ[n,0] || EqQ[g,0],
    (f+g*x)^n \[Star] Int122[d,e,m,a,b,c,p,x],
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int112[d,e,m,f,g,n,x],
  If[EqQ[c,0],
    Int113[d,e,m,f,g,n,a,b,p,x],
  Defer[Int123][(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.4:  Int[(a+b x+c x^2)^p (d+e x+f x^2)^q, x] \[RightArrow] Int124[a, b, c, p, d, e, f, q, x]*)


Int[(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] := Int124[a,b,c,p,d,e,f,q,x] /;
  FreeQ[{a,b,c,p,d,e,f,q},x]

Int[(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] := Int124[a,b,c,p,d,0,f,q,x] /;
  FreeQ[{a,b,c,p,d,f,q},x]


Int124::usage =
  "Int124[a,b,c,p,d,e,f,q,x] returns the antiderivative of (a+b x+c x^2)^p (d+e x+f x^2)^q wrt x.";


Int124[a_,b_,c_,p_,d_,e_,f_,q_,x_] :=
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int121[d,e,f,q,x],
  If[EqQ[q,0],
    (d+e*x+f*x^2)^q \[Star] Int121[a,b,c,p,x],
  If[EqQ[c,0],
    Int122[a,b,p,d,e,f,q,x],
  If[EqQ[f,0],
    Int122[d,e,q,a,b,c,p,x],
  If[EqQ[b,0] && EqQ[e,0],
    Int153[a,c,p,d,f,q,2,x],
  Defer[Int124][(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.5:  Int[(g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q, x] \[RightArrow] Int125[g, h, m, a, b, c, p, d, e, f, q, x]*)
(**)


Int[(g_.*x_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] := Int125[g,h,m,a,b,c,p,d,e,f,q,x] /;
  FreeQ[{g,h,m,a,b,c,p,d,e,f,q},x]

Int[(g_.*x_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] := Int125[g,h,m,a,b,c,p,d,0,f,q,x] /;
  FreeQ[{g,h,m,a,b,c,p,d,f,q},x]

Int[(g_.*x_+h_.*x_)^m_.*(a_.+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] := Int125[g,h,m,a,0,c,p,d,0,f,q,x] /;
  FreeQ[{g,h,m,a,c,p,d,f,q},x]


Int125::usage =
  "Int125[g,h,m,a,b,c,p,d,e,f,q,x] returns the antiderivative of (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q wrt x.";


Int125[g_,h_,m_,a_,b_,c_,p_,d_,e_,f_,q_,x_] :=
  If[EqQ[m,0] || EqQ[h,0],
    (g+h*x)^m \[Star] Int124[a,b,c,p,d,e,f,q,x],
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int122[g,h,m,d,e,f,q,x],
  If[EqQ[q,0],
    (d+e*x+f*x^2)^q \[Star] Int122[g,h,m,a,b,c,p,x],
  If[EqQ[c,0],
    Int123[g,h,m,a,b,p,d,e,f,q,x],
  If[EqQ[f,0],
    Int123[g,h,m,d,e,q,a,b,c,p,x],
  If[EqQ[b,0] && EqQ[e,0] && EqQ[g,0],
    Int154[h,m,a,c,p,d,f,q,2,x],
  Defer[Int125][(g+h*x)^m*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.6:  Int[P[x] (a+b x+c x^2)^p, x] \[RightArrow] Int126[P[x], a, b, c, p, x]*)


Int[Px_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] := Int126[Px,a,b,c,p,x] /;
  FreeQ[{a,b,c,p},x] && PolyQ[Px,x]


Int126::usage =
  "If P[x] is a polynomial in x, Int126[P[x],a,b,c,p,x] returns the antiderivative of P[x] (a+b x+c x^2)^p wrt x.";


Int126[Px_,a_,b_,c_,p_,x_] :=
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int[Px,x],
  If[EqQ[c,0],
    Int115[Px,a,b,p,x],
  If[EqQ[b,0],
    Int157[Px,a,c,p,2,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int121[a,b,c,p,x],
  If[PolyQ[Px,x,1],
    Int122[Coeff[Px,x,0],Coeff[Px,x,1],1,a,b,c,p,x],
  If[PolyQ[Px,x,2],
    Int124[Coeff[Px,x,0],Coeff[Px,x,1],Coeff[Px,x,2],1,a,b,c,p,x],
  Defer[Int126][Px*(a+b*x+c*x^2)^p,x]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.7:  Int[P[x] (d+e x)^m (a+b x+c x^2)^p, x] \[RightArrow] Int127[P[x], d, e, m, a, b, c, p, x]*)


Int[Px_*(d_.*e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] := Int127[Px,d,e,m,a,b,c,p,x] /;
  FreeQ[{d,e,m,a,b,c,p},x] && PolyQ[Px,x]

Int[Px_*(d_.*e_.*x_)^m_.*(a_.+c_.*x_^2)^p_.,x_Symbol] := Int127[Px,d,e,m,a,0,c,p,x] /;
  FreeQ[{d,e,m,a,c,p},x] && PolyQ[Px,x]


Int127::usage =
  "If P[x] is a polynomial in x, Int127[P[x],d,e,m,a,b,c,p,x] returns the antiderivative of P[x] (d+e x)^m (a+b x+c x^2)^p wrt x.";


Int127[Px_,d_,e_,m_,a_,b_,c_,p_,x_] :=
  If[EqQ[m,0] || EqQ[e,0],
    (d+e*x)^m \[Star] Int126[Px,a,b,c,p,x],
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int115[Px,d,e,m,x],
  If[EqQ[c,0],
    Int116[Px,d,e,m,a,b,p,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int122[d,e,m,a,b,c,p,x],
  If[PolyQ[Px,x,1],
    Int123[Coeff[Px,x,0],Coeff[Px,x,1],1,d,e,m,a,b,c,p,x],
  If[PolyQ[Px,x,2],
    Int125[d,e,m,Coeff[Px,x,0],Coeff[Px,x,1],Coeff[Px,x,2],1,a,b,c,p,x],
  Defer[Int127][Px*(d+e*x)^m*(a+b*x+c*x^2)^p,x]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.8:  Int[P[x] (d+e x)^m (f+g x)^n (a+b x+c x^2)^p, x] \[RightArrow] Int128[P[x], d, e, m, f, g, n, a, b, c, p, x]*)


Int[Px_*(d_.*e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] := Int128[Px,d,e,m,f,g,n,a,b,c,p,x] /;
  FreeQ[{d,e,m,f,g,n,a,b,c,p},x] && PolyQ[Px,x]

Int[Px_*(d_.*e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+c_.*x_^2)^p_.,x_Symbol] := Int128[Px,d,e,m,f,g,n,a,0,c,p,x] /;
  FreeQ[{d,e,m,f,g,n,a,c,p},x] && PolyQ[Px,x]


Int128::usage =
  "If P[x] is a polynomial in x, Int128[P[x],d,e,m,f,g,n,a,b,c,p,x] returns the antiderivative of P[x] (d+e x)^m (f+g x)^n (a+b x+c x^2)^p wrt x.";


Int128[Px_,d_,e_,m_,f_,g_,n_,a_,b_,c_,p_,x_] :=
  If[EqQ[m,0] || EqQ[e,0],
    (d+e*x)^m \[Star] Int127[Px,f,g,n,a,b,c,p,x],
  If[EqQ[n,0] || EqQ[g,0],
    (f+g*x)^n \[Star] Int127[Px,d,e,m,a,b,c,p,x],
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int116[d,e,m,f,g,n,x],
  If[EqQ[c,0],
    Int117[Px,d,e,m,f,g,n,a,b,p,x],
  Defer[Int128][Px*(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.9:  Int[P[x] (a+b x+c x^2)^p (d+e x+f x^2)^q, x] \[RightArrow] Int129[P[x], a, b, c, p, d, e, f, q, x]*)


Int[Px_*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] := Int129[Px,a,b,c,p,d,e,f,q,x] /;
  FreeQ[{a,b,c,p,d,e,f,q},x] && PolyQ[Px,x]

Int[Px_*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] := Int129[Px,a,b,c,p,d,0,f,q,x] /;
  FreeQ[{a,b,c,p,d,f,q},x] && PolyQ[Px,x]


Int129::usage =
  "If P[x] is a polynomial in x, Int129[P[x],a,b,c,p,d,e,f,q,x] returns the antiderivative of P[x] (a+b x+c x^2)^p (d+e x+f x^2)^q wrt x.";


Int129[Px_,a_,b_,c_,p_,d_,e_,f_,q_,x_] :=
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int126[Px,d,e,f,q,x],
  If[EqQ[q,0],
    (d+e*x+f*x^2)^q \[Star] Int126[Px,a,b,c,p,x],
  If[EqQ[c,0],
    Int127[Px,a,b,p,d,e,f,q,x],
  If[EqQ[f,0],
    Int127[Px,d,e,q,a,b,c,p,x],
  If[EqQ[b,0] && EqQ[e,0],
    Int159[Px,a,c,p,d,f,q,2,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int124[a,b,c,p,d,e,f,q,x],
  If[PolyQ[Px,x,1],
    Int125[Coeff[Px,x,0],Coeff[Px,x,1],1,a,b,c,p,d,e,f,q,x],
  Defer[Int129][Px*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x]]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.2.10:  Int[P[x] (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q, x] \[RightArrow] Int1210[P[x], g, h, m, a, b, c, p, d, e, f, q, x]*)


Int[Px_*(g_.*x_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] := Int1210[Px,g,h,m,a,b,c,p,d,e,f,q,x] /;
  FreeQ[{g,h,m,a,b,c,p,d,e,f,q},x] && PolyQ[Px,x]

Int[Px_*(g_.*x_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.,x_Symbol] := Int1210[Px,g,h,m,a,b,c,p,d,0,f,q,x] /;
  FreeQ[{g,h,m,a,b,c,p,d,f,q},x] && PolyQ[Px,x]


Int1210::usage =
  "If P[x] is a polynomial in x, Int1210[P[x],g,h,m,a,b,c,p,d,e,f,q,x] returns the antiderivative of P[x] (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q wrt x.";


Int1210[Px_,g_,h_,m_,a_,b_,c_,p_,d_,e_,f_,q_,x_] :=
  If[EqQ[m,0] || EqQ[h,0],
    (g+h*x)^m \[Star] Int129[Px,a,b,c,p,d,e,f,q,x],
  If[EqQ[p,0],
    (a+b*x+c*x^2)^p \[Star] Int127[Px,g,h,m,d,e,f,q,x],
  If[EqQ[q,0],
    (d+e*x+f*x^2)^q \[Star] Int127[Px,g,h,m,a,b,c,p,x],
  If[EqQ[c,0],
    Int128[Px,g,h,m,a,b,p,d,e,f,q,x],
  If[EqQ[f,0],
    Int128[Px,g,h,m,d,e,q,a,b,c,p,x],
  If[EqQ[b,0] && EqQ[e,0] && EqQ[g,0],
    Int1510[h,m,Px,a,c,p,d,f,q,2,x],
  If[EqQ[Px,0],
    0,
  If[PolyQ[Px,x,0],
    Px \[Star] Int125[g,h,m,a,b,c,p,d,e,f,q,x],
  Defer[Int1210][Px*(g+h*x)^m*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x]]]]]]]]]


(* ::Subsection::Closed:: *)
(*1.3 Cubic*)


(* ::Subsubsection::Closed:: *)
(*Rule 1.3.1:  Int[(a+b x+c x^2+d x^3)^p, x] \[RightArrow] Int131[a, b, c, d, p, x]*)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] := Int131[a,b,c,d,p,x] /;
  FreeQ[{a,b,c,d,p},x]

Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] := Int131[a,b,0,d,p,x] /;
  FreeQ[{a,b,d,p},x]

Int[(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] := Int131[a,0,c,d,p,x] /;
  FreeQ[{a,c,d,p},x]


Int131::usage =
  "Int131[a,b,c,d,p,x] returns the antiderivative of (a+b x+c x^2+d x^3)^p wrt x.";


Int131[a_,b_,c_,d_,p_,x_] :=
  If[EqQ[d,0],
    Int121[a,b,c,p,x],
  If[EqQ[b,0] && EqQ[c,0],
    Int151[a,d,p,3],
  Defer[Int131][(a+b*x+c*x^2+d*x^3)^p,x]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.3.2:  Int[(e+f x)^m (a+b x+c x^2+d x^3)^p, x] \[RightArrow] Int132[e, f, m, a, b, c, d, p, x]*)


Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] := Int132[e,f,m,a,b,c,d,p,x] /;
  FreeQ[{e,f,m,a,b,c,d,p},x]

Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] := Int132[e,f,m,a,b,0,d,p,x] /;
  FreeQ[{e,f,m,a,b,d,p},x]

Int[(e_.+f_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] := Int132[e,f,m,a,0,c,d,p,x] /;
  FreeQ[{e,f,m,a,c,d,p},x]


Int132::usage =
  "Int132[e,f,m,a,b,c,d,p,x] returns the antiderivative of (e+f x)^m (a+b x+c x^2+d x^3)^p wrt x.";


Int132[e_,f_,m_,a_,b_,c_,d_,p_,x_] :=
  If[EqQ[d,0],
    Int122[e,f,m,a,b,c,p,x],
  Defer[Int132][(e+f*x)^m*(a+b*x+c*x^2+d*x^3)^p,x]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.3.3:  Int[(e+f x)^m (g+h x)^n (a+b x+c x^2+d x^3)^p, x] \[RightArrow] Int133[e, f, m, g, h, n, a, b, c, d, p, x]*)


Int[(e_.+f_.*x_)^m_.*(g_.+h_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] := Int133[e,f,m,g,h,n,a,b,c,d,p,x] /;
  FreeQ[{e,f,m,g,h,n,a,b,c,d,p},x]

Int[(e_.+f_.*x_)^m_.*(g_.+h_.*x_)^n_.*(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] := Int133[e,f,m,g,h,n,a,b,0,d,p,x] /;
  FreeQ[{e,f,m,g,h,n,a,b,d,p},x]

Int[(e_.+f_.*x_)^m_.*(g_.+h_.*x_)^n_.*(a_.+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] := Int133[e,f,m,g,h,n,a,0,c,d,p,x] /;
  FreeQ[{e,f,m,g,h,n,a,c,d,p},x]


Int133::usage =
  "Int133[e,f,m,g,h,n,a,b,c,d,p,x] returns the antiderivative of (e+f x)^m (g+h x)^n (a+b x+c x^2+d x^3)^p wrt x.";


Int133[e_,f_,m_,g_,h_,n_,a_,b_,c_,d_,p_,x_] :=
  If[EqQ[d,0],
    Int123[e,f,m,g,h,n,a,b,c,p,x],
  Defer[Int133][(e+f*x)^m*(g+h*x)^n*(a+b*x+c*x^2+d*x^3)^p,x]]


(* ::Subsection::Closed:: *)
(*1.4 Quartic*)


(* ::Subsubsection::Closed:: *)
(*Rule 1.4.1:  Int[(a+b x+c x^2+d x^3+e x^4)^p, x] \[RightArrow] Int141[a, b, c, d, e, p, x]*)


Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int141[a,b,c,d,e,p,x] /;
  FreeQ[{a,b,c,d,e,p},x]

Int[(a_.+b_.*x_+c_.*x_^2+e_.*x_^4)^p_,x_Symbol] := Int141[a,b,c,0,e,p,x] /;
  FreeQ[{a,b,c,e,p},x]

Int[(a_.+b_.*x_+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int141[a,b,0,d,e,p,x] /;
  FreeQ[{a,b,d,e,p},x]

Int[(a_.+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int141[a,0,c,d,e,p,x] /;
  FreeQ[{a,c,d,e,p},x]

Int[(a_.+b_.*x_+e_.*x_^4)^p_,x_Symbol] := Int141[a,b,0,0,e,p,x] /;
  FreeQ[{a,b,e,p},x]

Int[(a_.+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int141[a,0,0,d,e,p,x] /;
  FreeQ[{a,d,e,p},x]


Int141::usage =
  "Int141[a,b,c,d,e,p,x] returns the antiderivative of (a+b x+c x^2+d x^3+e x^4)^p wrt x.";


Int141[a_,b_,c_,d_,e_,p_,x_] :=
  If[EqQ[e,0],
    Int131[a,b,c,d,p,x],
  Defer[Int141][(a+b*x+c*x^2+d*x^3+e*x^4)^p,x]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.4.2:  Int[(f+g x)^m (a+b x+c x^2+d x^3+e x^4)^p, x] \[RightArrow] Int142[f, g, m, a, b, c, d, e, p, x]*)


Int[(f_.+g_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int142[f,g,m,a,b,c,d,e,p,x] /;
  FreeQ[{f,g,m,a,b,c,d,e,p},x]

Int[(f_.+g_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+e_.*x_^4)^p_,x_Symbol] := Int142[f,g,m,a,b,c,0,e,p,x] /;
  FreeQ[{f,g,m,a,b,c,e,p},x]

Int[(f_.+g_.*x_)^m_.*(a_.+b_.*x_+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int142[f,g,m,a,b,0,d,e,p,x] /;
  FreeQ[{f,g,m,a,b,d,e,p},x]

Int[(f_.+g_.*x_)^m_.*(a_.+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int142[f,g,m,a,0,c,d,e,p,x] /;
  FreeQ[{f,g,m,a,c,d,e,p},x]

Int[(f_.+g_.*x_)^m_.*(a_.+b_.*x_+e_.*x_^4)^p_,x_Symbol] := Int142[f,g,m,a,b,0,0,e,p,x] /;
  FreeQ[{f,g,m,a,b,e,p},x]

Int[(f_.+g_.*x_)^m_.*(a_.+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int142[f,g,m,a,0,0,d,e,p,x] /;
  FreeQ[{f,g,m,a,d,e,p},x]


Int142::usage =
  "Int142[f,g,m,a,b,c,d,e,p,x] returns the antiderivative of (f+g x)^m (a+b x+c x^2+d x^3+e x^4)^p wrt x.";


Int142[f_,g_,m_,a_,b_,c_,d_,e_,p_,x_] :=
  If[EqQ[e,0],
    Int132[f,g,m,a,b,c,d,p,x],
  Defer[Int142][(f+g*x)^m*(a+b*x+c*x^2+d*x^3+e*x^4)^p,x]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.4.3:  Int[(f+g x)^m (h+i x)^n (a+b x+c x^2+d x^3+e x^4)^p, x] \[RightArrow] Int143[f, g, m, h, i, n, a, b, c, d, e, p, x]*)


Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int143[f,g,m,h,i,n,a,b,c,d,e,p,x] /;
  FreeQ[{f,g,m,h,i,n,a,b,c,d,e,p},x]

Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2+e_.*x_^4)^p_,x_Symbol] := Int143[f,g,m,h,i,n,a,b,c,0,e,p,x] /;
  FreeQ[{f,g,m,h,i,n,a,b,c,e,p},x]

Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^n_*(a_.+b_.*x_+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int143[f,g,m,h,i,n,a,b,0,d,e,p,x] /;
  FreeQ[{f,g,m,h,i,n,a,b,d,e,p},x]

Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^n_*(a_.+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int143[f,g,m,h,i,n,a,0,c,d,e,p,x] /;
  FreeQ[{f,g,m,h,i,n,a,c,d,e,p},x]

Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^n_*(a_.+b_.*x_+e_.*x_^4)^p_,x_Symbol] := Int143[f,g,m,h,i,n,a,b,0,0,e,p,x] /;
  FreeQ[{f,g,m,h,i,n,a,b,e,p},x]

Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^n_*(a_.+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] := Int143[f,g,m,h,i,n,a,0,0,d,e,p,x] /;
  FreeQ[{f,g,m,h,i,n,a,d,e,p},x]


Int143::usage =
  "Int143[f,g,m,h,i,n,a,b,c,d,e,p,x] returns the antiderivative of (f+g x)^m (h+i x)^n (a+b x+c x^2+d x^3+e x^4)^p wrt x.";


Int143[f_,g_,m_,h_,i_,n_,a_,b_,c_,d_,e_,p_,x_] :=
  If[EqQ[e,0],
    Int133[f,g,m,h,i,n,a,b,c,d,p,x],
  Defer[Int143][(f+g*x)^m*(h+i*x)^n*(a+b*x+c*x^2+d*x^3+e*x^4)^p,x]]


(* ::Subsection::Closed:: *)
(*1.5 Binomial*)


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.1:  Int[(a+b x^n)^p, x], x] \[RightArrow] Int151[a, b, p, n, x]*)


Int[(a_.+b_.*x_^n_)^p_.,x_Symbol] := Int151[a,b,p,n,x] /;
  FreeQ[{a,b,p,n},x]


Int151::usage =
  "Int151[a,b,p,n,x] returns the antiderivative of (a+b x^n)^p wrt x.";


Int151[a_,b_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p*x,
  If[EqQ[n,1],
    Int111[a,b,p,x],
  If[EqQ[p,1],
    a*x + b \[Star] Int111[0,1,n,x],
  Defer[Int151][(a+b*x^n)^p,x]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.2:  Int[(c x)^m (a+b x^n)^p, x] \[RightArrow] Int152[c, m, a, b, p, n, x]*)


Int[(c_.*x_)^m_.*(a_.+b_.*x_^n_)^p_.,x_Symbol] := Int152[c,m,a,b,p,n,x] /;
  FreeQ[{c,m,a,b,p,n},x]


Int152::usage =
  "Int152[c,m,a,b,p,n,x] returns the antiderivative of (c x)^m (a+b x^n)^p wrt x.";


Int152[c_,m_,a_,b_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int111[0,c,m,x],
  If[EqQ[m,0] || EqQ[c,0],
    (c*x)^m \[Star] Int151[a,b,p,n,x],
  If[EqQ[n,1],
    Int112[0,c,m,a,b,p,x],
  Defer[Int152][(c*x)^m*(a+b*x^n)^p,x]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.3:  Int[(a+b x^n)^p (c+d x^n)^q, x] \[RightArrow] Int153[a, b, p, c, d, q, n, x]*)


Int[(a_.+b_.*x_^n_)^p_.*(c_.+d_.*x_^n_)^q_.,x_Symbol] := Int153[a,b,p,c,d,q,n,x] /;
  FreeQ[{a,b,p,c,d,q,n},x]


Int153::usage =
  "Int153[a,b,p,c,d,q,n,x] returns the antiderivative of (a+b x^n)^p (c+d x^n)^q wrt x.";


Int153[a_,b_,p_,c_,d_,q_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int151[c,d,q,n,x],
  If[EqQ[q,0] || EqQ[d,0],
    (c+d*x^n)^q \[Star] Int151[a,b,p,n,x],
  If[EqQ[n,1],
    Int112[a,b,p,c,d,q,x],
  Defer[Int153][(a+b*x^n)^p*(c+d*x^n)^q,x]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.4:  Int[(e x)^m (a+b x^n)^p (c+d x^n)^q, x] \[RightArrow] Int154[e, m, a, b, p, c, d, q, n, x]*)


Int[(e_.*x_)^m_.*(a_.+b_.*x_^n_)^p_.*(c_.+d_.*x_^n_)^q_.,x_Symbol] := Int154[e,m,a,b,p,c,d,q,n,x] /;
  FreeQ[{e,m,a,b,p,c,d,q,n},x]


Int154::usage =
  "Int154[e,m,a,b,p,c,d,q,n,x] returns the antiderivative of (e x)^m (a+b x^n)^p (c+d x^n)^q wrt x.";


Int154[e_,m_,a_,b_,p_,c_,d_,q_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int152[e,m,c,d,q,n,x],
  If[EqQ[q,0] || EqQ[d,0],
    (c+d*x^n)^q \[Star] Int152[e,m,a,b,p,n,x],
  If[EqQ[m,0] || EqQ[e,0],
    (e*x)^m \[Star] Int153[a,b,p,c,d,q,n,x],
  If[EqQ[n,1],
    Int113[0,e,m,a,b,p,c,d,q,x],
  Defer[Int154][(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.5:  Int[(a+b x^n)^p (c+d x^n)^q (e+f x^n)^r, x] \[RightArrow] Int155[a, b, p, c, d, q, e, f, r, n, x]*)


Int[(a_.+b_.*x_^n_)^p_.*(c_.+d_.*x_^n_)^q_.*(e_.+f_.*x_^n_)^r_.,x_Symbol] := Int155[a,b,p,c,d,q,e,f,r,n,x] /;
  FreeQ[{a,b,p,c,d,q,e,f,r,n},x]


Int155::usage =
  "Int155[a,b,p,c,d,q,e,f,r,n,x] returns the antiderivative of (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r wrt x.";


Int155[a_,b_,p_,c_,d_,q_,e_,f_,r_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int153[c,d,q,e,f,r,n,x],
  If[EqQ[q,0] || EqQ[d,0],
    (c+d*x^n)^q \[Star] Int153[a,b,p,e,f,r,n,x],
  If[EqQ[r,0] || EqQ[f,0],
    (e+f*x^n)^r \[Star] Int153[a,b,p,c,d,q,n,x],
  If[EqQ[n,1],
    Int113[a,b,p,c,d,q,e,f,r,x],
  Defer[Int155][(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.6:  Int[(g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r, x] \[RightArrow] Int156[g, m, a, b, p, c, d, q, e, f, r, n, x]*)
(**)


Int[(g_.*x_)^m_.*(a_.+b_.*x_^n_)^p_.*(c_.+d_.*x_^n_)^q_.*(e_.+f_.*x_^n_)^r_.,x_Symbol] := Int156[g,m,a,b,p,c,d,q,e,f,r,n,x] /;
  FreeQ[{g,m,a,b,p,c,d,q,e,f,r,n},x]


Int156::usage =
  "Int156[g,m,a,b,p,c,d,q,e,f,r,n,x] returns the antiderivative of (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r wrt x.";


Int156[g_,m_,a_,b_,p_,c_,d_,q_,e_,f_,r_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int154[g,m,c,d,q,e,f,r,n,x],
  If[EqQ[q,0] || EqQ[d,0],
    (c+d*x^n)^q \[Star] Int154[g,m,a,b,p,e,f,q,n,x],
  If[EqQ[r,0] || EqQ[f,0],
    (e+f*x^n)^r \[Star] Int154[g,m,a,b,p,c,d,q,n,x],
  If[EqQ[m,0] || EqQ[g,0],
    (g*x)^m \[Star] Int155[a,b,p,c,d,q,e,f,r,n,x],
  If[EqQ[n,1],
    Int114[0,g,m,a,b,p,c,d,q,e,f,r,x],
  Defer[Int156][(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.7:  Int[P[x] (a+b x^n)^p, x] \[RightArrow] Int157[P[x], a, b, p, n, x]*)


Int[Px_*(a_.+b_.*x_^n_)^p_.,x_Symbol] := Int157[Px,a,b,p,n,x] /;
  FreeQ[{a,b,p,n},x] && PolyQ[Px,x]


Int157::usage =
  "If P[x] is a polynomial in x, Int157[P[x],a,b,p,n,x] returns the antiderivative of P[x] (a+b x^n)^p wrt x.";


Int157[Px_,a_,b_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int[Px,x],
  If[EqQ[n,1],
    Int115[Px,a,b,p,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int151[a,b,p,n,x],
  If[PolyQ[Px,x^n,1],
    Int153[a,b,p,Coeff[Px,x^n,0],Coeff[Px,x^n,1],1,n,x],
  If[PolyQ[Px,x^n,2],
    Int163[a,b,p,Coeff[Px,x^n,0],Coeff[Px,x^n,1],Coeff[Px,x^n,2],1,n,x],
  Defer[Int157][Px*(a+b*x^n)^p,x]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.8:  Int[(c x)^m P[x] (a+b x^n)^p, x] \[RightArrow] Int158[c, m, P[x], a, b, p, n, x]*)


Int[(c_.*x_)^m_.*Px_*(a_.+b_.*x_^n_)^p_.,x_Symbol] := Int158[c,m,Px,a,b,p,n,x] /;
  FreeQ[{c,m,a,b,p,n},x] && PolyQ[Px,x]


Int158::usage =
  "If P[x] is a polynomial in x, Int158[c,m,P[x],a,b,p,n,x] returns the antiderivative of (c x)^m P[x] (a+b x^n)^p wrt x.";


Int158[c_,m_,Px_,a_,b_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int115[Px,0,c,m,x],
  If[EqQ[m,0] || EqQ[c,0],
    (c*x)^m \[Star] Int157[Px,a,b,p,n,x],
  If[EqQ[n,1],
    Int116[Px,0,c,m,a,b,p,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int152[c,m,a,b,p,n,x],
  If[PolyQ[Px,x^n,1],
    Int154[c,m,a,b,p,Coeff[Px,x^n,0],Coeff[Px,x^n,1],1,n,x],
  If[PolyQ[Px,x^n,2],
    Int164[c,m,a,b,p,Coeff[Px,x^n,0],Coeff[Px,x^n,1],Coeff[Px,x^n,2],1,n,x],
  Defer[Int158][(c*x)^m*Px*(a+b*x^n)^p,x]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.9:  Int[P[x] (a+b x^n)^p (c+d x^n)^q, x] \[RightArrow] Int159[P[x], a, b, p, c, d, q, n, x]*)


Int[Px_*(a_.+b_.*x_^n_)^p_.*(c_.+d_.*x_^n_)^q_.,x_Symbol] := Int159[Px,a,b,p,c,d,q,n,x] /;
  FreeQ[{a,b,p,c,d,q,n},x] && PolyQ[Px,x]


Int159::usage =
  "If P[x] is a polynomial in x, Int159[P[x],a,b,p,c,d,q,n,x] returns the antiderivative of P[x] (a+b x^n)^p (c+d x^n)^q wrt x.";


Int159[Px_,a_,b_,p_,c_,d_,q_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int157[Px,c,d,q,n,x],
  If[EqQ[q,0] || EqQ[d,0],
    (c+d*x^n)^q \[Star] Int157[Px,a,b,p,n,x],
  If[EqQ[n,1],
    Int116[Px,a,b,p,c,d,q,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int153[a,b,p,c,d,q,n,x],
  If[PolyQ[Px,x^n,1],
    Int155[a,b,p,c,d,q,Coeff[Px,x^n,0],Coeff[Px,x^n,1],1,n,x],
  If[PolyQ[Px,x^n,2] && EqQ[a,0] && IntegerQ[p],
    b^p \[Star] Int164[1,n*p,c,d,q,Coeff[Px,x^n,0],Coeff[Px,x^n,1],Coeff[Px,x^n,2],1,n,x],
  If[PolyQ[Px,x^n,2] && EqQ[c,0] && IntegerQ[q],
    d^q \[Star] Int164[1,n*q,a,b,p,Coeff[Px,x^n,0],Coeff[Px,x^n,1],Coeff[Px,x^n,2],1,n,x],
  Defer[Int159][Px*(a+b*x^n)^p*(c+d*x^n)^q,x]]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.5.10:  Int[(e x)^m P[x] (a+b x^n)^p (c+d x^n)^q, x] \[RightArrow] Int1510[e, m, P[x], a, b, p, c, d, q, n, x]*)


Int[(e_.*x_)^m_.*Px_*(a_.+b_.*x_^n_)^p_.*(c_.+d_.*x_^n_)^q_.,x_Symbol] := Int1510[e,m,Px,a,b,p,c,d,q,n,x] /;
  FreeQ[{e,m,a,b,p,c,d,q,n},x] && PolyQ[Px,x]


Int1510::usage =
  "If P[x] is a polynomial in x, Int1510[e,m,P[x],a,b,p,c,d,q,n,x] returns the antiderivative of (e x)^m P[x] (a+b x^n)^p (c+d x^n)^q wrt x.";


Int1510[Px_,e_,m_,a_,b_,p_,c_,d_,q_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0] || EqQ[b,0],
    (a+b*x^n)^p \[Star] Int158[e,m,Px,c,d,q,n,x],
  If[EqQ[q,0] || EqQ[d,0],
    (c+d*x^n)^q \[Star] Int158[e,m,Px,a,b,p,n,x],
  If[EqQ[m,0] || EqQ[e,0],
    (e*x)^m \[Star] Int159[Px,a,b,p,c,d,q,n,x],
  If[EqQ[n,1],
    Int117[Px,0,e,m,a,b,p,c,d,q,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int154[e,m,a,b,p,c,d,q,n,x],
  If[PolyQ[Px,x^n,1],
    Int156[e,m,a,b,p,c,d,q,Coeff[Px,x^n,0],Coeff[Px,x^n,1],1,n,x],
  Defer[Int1510][(e*x)^m*Px*(a+b*x^n)^p*(c+d*x^n)^q,x]]]]]]]]


(* ::Subsection::Closed:: *)
(*1.6 Trinomial*)


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.1:  Int[(a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int161[a, b, c, p, n, x]*)


Int[(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int161[a,b,c,p,n,x] /;
  FreeQ[{a,b,c,p,n},x] && EqQ[n2,2*n]


Int161::usage =
  "Int161[a,b,c,p,n,x] returns the antiderivative of (a+b x^n+c x^(2 n))^p wrt x.";


Int161[a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p*x,
  If[EqQ[c,0],
    Int151[a,b,p,n,x],
  If[EqQ[b,0],
    Int151[a,c,p,2*n,x],
  If[EqQ[p,1],
    a*x + b \[Star] Int111[0,1,n,x] + c \[Star] Int111[0,1,2*n,x],
  If[EqQ[n,1],
    Int121[a,b,c,p,x],
  Defer[Int161][(a+b*x^n+c*x^(2*n))^p,x]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.2:  Int[(d x)^m (a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int162[d, m, a, b, c, p, n, x]*)


Int[(d_.*x_)^m_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int162[d,m,a,b,c,p,n,x] /;
  FreeQ[{d,m,a,b,c,p,n},x] && EqQ[n2,2*n]


Int162::usage =
  "Int162[d,m,a,b,c,p,n,x] returns the antiderivative of (d x)^m (a+b x^n+c x^(2 n))^p wrt x.";


Int162[d_,m_,a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p \[Star] Int111[0,d,m,x],
  If[EqQ[m,0] || EqQ[d,0],
    (d*x)^m \[Star] Int161[a,b,c,p,n,x],
  If[EqQ[c,0],
    Int152[d,m,a,b,p,n,x],
  If[EqQ[b,0],
    Int152[d,m,a,c,p,2*n,x],
  If[EqQ[p,1],
    Int152[d,m,a,b,1,n,x] + c \[Star] Int112[0,d,m,0,1,2*n,x],
  If[EqQ[n,1],
    Int122[0,d,m,a,b,c,p,x],
  Defer[Int162][(d*x)^m*(a+b*x^n+c*x^(2*n))^p,x]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.3:  Int[(d+e x^n)^q (a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int163[d, e, q, a, b, c, p, n, x]*)


Int[(d_.+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int163[d,e,q,a,b,c,p,n,x] /;
  FreeQ[{d,e,q,a,b,c,p,n},x] && EqQ[n2,2*n]

Int[(d_.+e_.*x_^n_)^q_.*(a_.+c_.*x_^n2_.)^p_.,x_Symbol] := Int163[d,e,q,a,0,c,p,n,x] /;
  FreeQ[{d,e,q,a,c,p,n},x] && EqQ[n2,2*n]


Int163::usage =
  "Int163[d,e,q,a,b,c,p,n,x] returns the antiderivative of (d+e x^n)^q (a+b x^n+c x^(2 n))^p wrt x.";


Int163[d_,e_,q_,a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[q,0] || EqQ[e,0],
    (d+e*x^n)^q \[Star] Int161[a,b,c,p,n,x],
  If[EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p \[Star] Int151[d,e,q,n,x],
  If[EqQ[c,0],
    Int153[d,e,q,a,b,p,n,x],
  If[EqQ[n,1],
    Int122[d,e,q,a,b,c,p,x],
  Defer[Int163][(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.4:  Int[(f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int164[f, m, d, e, q, a, b, c, p, n, x]*)
(**)


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int164[f,m,d,e,q,a,b,c,p,n,x] /;
  FreeQ[{f,m,d,e,q,a,b,c,p,n},x] && EqQ[n2,2*n]

Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_.*(a_.+c_.*x_^n2_.)^p_.,x_Symbol] := Int164[f,m,d,e,q,a,0,c,p,n,x] /;
  FreeQ[{f,m,d,e,q,a,c,p,n},x] && EqQ[n2,2*n]


Int164::usage =
  "Int164[f,m,d,e,q,a,b,c,p,n,x] returns the antiderivative of (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p wrt x.";


Int164[f_,m_,d_,e_,q_,a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[q,0] || EqQ[e,0],
    (d+e*x^n)^q \[Star] Int162[f,m,a,b,c,p,n,x],
  If[EqQ[m,0] || EqQ[f,0],
    (f*x)^m \[Star] Int163[d,e,q,a,b,c,p,n,x],
  If[EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p \[Star] Int152[f,m,d,e,q,n,x],
  If[EqQ[c,0],
    Int154[f,m,d,e,q,a,b,p,n,x],
  If[EqQ[n,1],
    Int123[0,f,m,d,e,q,a,b,c,p,x],
  Defer[Int164][(f*x)^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.5:  Int[P[x] (a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int165[P[x], a, b, c, p, n, x]*)


Int[Px_*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int165[Px,a,b,c,p,n,x] /;
  FreeQ[{a,b,c,p,n},x] && EqQ[n2,2*n] && PolyQ[Px,x]


Int165::usage =
  "If P[x] is a polynomial in x, Int165[P[x],a,b,c,p,n,x] returns the antiderivative of P[x] (a+b x^n+c x^(2 n))^p wrt x.";


Int165[Px_,a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p \[Star] Int[Px,x],
  If[EqQ[c,0],
    Int157[Px,a,b,p,n,x],
  If[EqQ[b,0],
    Int157[Px,a,c,p,2*n,x],
  If[EqQ[n,1],
    Int126[Px,a,b,c,p,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int161[a,b,c,p,n,x],
  If[PolyQ[Px,x^n,1],
    Int163[Coeff[Px,x^n,0],Coeff[Px,x^n,1],1,a,b,c,p,n,x],
  Defer[Int165][Px*(a+b*x^n+c*x^(2*n))^p,x]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.6:  Int[(d x)^m P[x] (a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int166[d, m, P[x], a, b, c, p, n, x]*)


Int[(d_.*x_)^m_.*Px_,(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int166[d,m,Px,a,b,c,p,n,x] /;
  FreeQ[{d,m,a,b,c,p,n},x] && EqQ[n2,2*n] && PolyQ[Px,x]


Int166::usage =
  "If P[x] is a polynomial in x, Int166[d,m,P[x],a,b,c,p,n,x] returns the antiderivative of (d x)^m P[x] (a+b x^n+c x^(2 n))^p wrt x.";


Int166[d_,m_,Px_,a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p \[Star] Int115[Px,0,d,m,x],
  If[EqQ[m,0] || EqQ[d,0],
    (d*x)^m \[Star] Int165[Px,a,b,c,p,n,x],
  If[EqQ[c,0],
    Int158[d,m,Px,a,b,p,n,x],
  If[EqQ[b,0],
    Int158[d,m,Px,a,c,p,2*n,x],
  If[EqQ[p,1],
    Int158[d,m,Px,a,b,1,n,x] + c \[Star] Int116[Px,0,d,m,0,1,2*n,x],
  If[EqQ[n,1],
    Int127[Px,0,d,m,a,b,c,p,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int162[d,m,a,b,c,p,n,x],
  If[PolyQ[Px,x^n,1],
    Int164[d,m,Coeff[Px,x^n,0],Coeff[Px,x^n,1],1,a,b,c,p,n,x],
  Defer[Int166][(d*x)^m*Px*(a+b*x^n+c*x^(2*n))^p,x]]]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.7:  Int[P[x] (d+e x^n)^q (a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int167[P[x], d, e, q, a, b, c, p, n, x]*)


Int[Px_*(d_.+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int167[Px,d,e,q,a,b,c,p,n,x] /;
  FreeQ[{d,e,q,a,b,c,p,n},x] && EqQ[n2,2*n] && PolyQ[Px,x]

Int[Px_*(d_.+e_.*x_^n_)^q_.*(a_.+c_.*x_^n2_.)^p_.,x_Symbol] := Int167[Px,d,e,q,a,0,c,p,n,x] /;
  FreeQ[{d,e,q,a,c,p,n},x] && EqQ[n2,2*n] && PolyQ[Px,x]


Int167::usage =
  "If P[x] is a polynomial in x, Int167[P[x],d,e,q,a,b,c,p,n,x] returns the antiderivative of P[x] (d+e x^n)^q (a+b x^n+c x^(2 n))^p wrt x.";


Int167[Px_,d_,e_,q_,a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[q,0] || EqQ[e,0],
    (d+e*x^n)^q \[Star] Int165[Px,a,b,c,p,n,x],
  If[EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p \[Star] Int157[Px,d,e,q,n,x],
  If[EqQ[c,0],
    Int159[Px,d,e,q,a,b,p,n,x],
  If[EqQ[n,1],
    Int127[Px,d,e,q,a,b,c,p,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int163[d,e,q,a,b,c,p,n,x],
  If[PolyQ[Px,x^n,1] && EqQ[d,0] && IntegerQ[q],
    e^q \[Star] Int164[1,n*q,Coeff[Px,x^n,0],Coeff[Px,x^n,1],1,a,b,c,p,n,x],
  Defer[Int167][Px*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x]]]]]]]]


(* ::Subsubsection::Closed:: *)
(*Rule 1.6.8:  Int[(f x)^m P[x] (d+e x^n)^q (a+b x^n+c x^(2 n))^p, x] \[RightArrow] Int168[f, m, P[x], d, e, q, a, b, c, p, n, x]*)
(**)


Int[(f_.*x_)^m_.*Px_*(d_.+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] := Int168[f,m,Px,d,e,q,a,b,c,p,n,x] /;
  FreeQ[{f,m,d,e,q,a,b,c,p,n},x] && EqQ[n2,2*n] && PolyQ[Px,x]

Int[(f_.*x_)^m_.*Px_*(d_.+e_.*x_^n_)^q_.*(a_.+c_.*x_^n2_.)^p_.,x_Symbol] := Int168[f,m,Px,d,e,q,a,0,c,p,n,x] /;
  FreeQ[{f,m,d,e,q,a,c,p,n},x] && EqQ[n2,2*n] && PolyQ[Px,x]


Int168::usage =
  "If P[x] is a polynomial in x, Int168[f,m,P[x],d,e,q,a,b,c,p,n,x] returns the antiderivative of (f x)^m P[x] (d+e x^n)^q (a+b x^n+c x^(2 n))^p wrt x.";


Int168[f_,m_,Px_,d_,e_,q_,a_,b_,c_,p_,n_,x_] :=
  If[EqQ[n,0] || EqQ[q,0] || EqQ[e,0],
    (d+e*x^n)^q \[Star] Int166[f,m,Px,a,b,c,p,n,x],
  If[EqQ[m,0] || EqQ[f,0],
    (f*x)^m \[Star] Int167[Px,d,e,q,a,b,c,p,n,x],
  If[EqQ[p,0],
    (a+b*x^n+c*x^(2*n))^p \[Star] Int158[f,m,Px,d,e,q,n,x],
  If[EqQ[c,0],
    Int1510[f,m,Px,d,e,q,a,b,p,n,x],
  If[EqQ[n,1],
    Int128[Px,0,f,m,d,e,q,a,b,c,p,x],
  If[EqQ[Px,0],
    0,
  If[FreeQ[Px,x],
    Px \[Star] Int164[f,m,d,e,q,a,b,c,p,n,x],
  Defer[Int168][(f*x)^m*Px*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x]]]]]]]]


(* ::Section:: *)
(*2 Exponentials*)


(* ::Section:: *)
(*3 Logarithms*)


(* ::Section::Closed:: *)
(*4 Trig Functions*)


(* ::Subsection:: *)
(*4.1 Sine*)


(* ::Subsection:: *)
(*4.3 Tangent*)


(* ::Subsection:: *)
(*4.5 Secant*)


(* ::Subsection:: *)
(*4.7 Miscellaneous Trig*)


(* ::Section::Closed:: *)
(*5 Inverse Trig Functions*)


(* ::Subsection:: *)
(*5.1 Inverse Sine*)


(* ::Subsection:: *)
(*5.3 Inverse Tangent*)


(* ::Subsection:: *)
(*5.5 Inverse Secant*)


(* ::Section::Closed:: *)
(*6 Hyperbolic Functions*)


(* ::Subsection:: *)
(*6.1 Hyperbolic Sine*)


(* ::Subsection:: *)
(*6.3 Hyperbolic Tangent*)


(* ::Subsection:: *)
(*6.5 Hyperbolic Secant*)


(* ::Subsection:: *)
(*6.7 Miscellaneous Hyperbolic*)


(* ::Section::Closed:: *)
(*7 Inverse Hyperbolic Functions*)


(* ::Subsection:: *)
(*71 Inverse Hyperbolic Sine*)


(* ::Subsection:: *)
(*7.3 Inverse Hyperbolic Tangent*)


(* ::Subsection:: *)
(*7.5 Inverse Hyperbolic Secant*)


(* ::Section:: *)
(*8 Special Functions*)


(* ::Section::Closed:: *)
(*9 Miscellaneous*)


Int[Fx_,x_Symbol] := Int[First[Fx],x]+Int[Rest[Fx],x] /; SumQ[Fx]


(* ::Title:: *)
(*Rubi 5 Utility Routines*)


(* ::Section::Closed:: *)
(*1 Predicate Routines*)


(* ::Subsection::Closed:: *)
(*Numeric type predicates*)


(* ::Subsubsection::Closed:: *)
(*FractionQ[u]*)


FractionQ::usage = "FractionQ[u] returns True if u is an explicit fraction; else it returns False.";


FractionQ[u_] := Head[u]===Rational


(* ::Subsubsection::Closed:: *)
(*RationalQ[u]*)


RationalQ::usage = "RationalQ[u] returns True if u is an explicit integer OR fraction; else it returns False.";


RationalQ[u_] := IntegerQ[u] || FractionQ[u]


(* ::Subsubsection::Closed:: *)
(*ComplexQ[u]*)


ComplexQ::usage = "ComplexQ[u] returns True if u an explicit complex number; else it returns False.";


ComplexQ[u_] := Head[u]===Complex


(* ::Subsection::Closed:: *)
(*Expression type predicates*)


(* ::Subsubsection::Closed:: *)
(*PowerQ[u]*)


PowerQ::usage = "PowerQ[u] returns True if u is a power; else it returns False.";


PowerQ[_Power] = True;
PowerQ[_] = False;


(* ::Subsubsection::Closed:: *)
(*ProductQ[u]*)


ProductQ::usage = "ProductQ[u] returns True if u is a product; else it returns False.";


ProductQ[_Times] = True;
ProductQ[_] = False;


(* ::Subsubsection::Closed:: *)
(*SumQ[u]*)


SumQ::usage = "SumQ[u] returns True if u is a sum; else it returns False.";


SumQ[_Plus] = True;
SumQ[_] = False;


(* ::Subsection::Closed:: *)
(*Expression form predicates*)


(* ::Subsubsection::Closed:: *)
(*PosQ[u]*)


PosQ::usage = "PosQ[u] returns True if u is nonzero and has a positive form, else it returns False.";


PosQ[u_] :=
  PosAux[Together[u]]

PosAux[u_] :=
  If[NumberQ[u],
    If[ComplexQ[u],
      If[EqQ[Re[u],0],
        PosAux[Im[u]],
      PosAux[Re[u]]],
    u>0],
  If[NumericQ[u],
    With[{v=Simplify[Re[u]]},
      If[NumberQ[v],
        If[EqQ[v,0],
          PosAux[Simplify[Im[u]]],
        v>0],
      With[{w=N[u]}, NumberQ[w] && PosAux[w]]]],
  With[{v=Refine[u>0]}, If[v===True || v===False,
    v,
  If[PowerQ[u],
    If[IntegerQ[u[[2]]],
      EvenQ[u[[2]]] || PosAux[u[[1]]],
    True],
  If[ProductQ[u],
    If[PosAux[First[u]],
      PosAux[Rest[u]],
    Not[PosAux[Rest[u]]]],
  If[SumQ[u],
    PosAux[First[u]],
  True]]]]]]]


(* ::Subsubsection::Closed:: *)
(*NegQ[u]*)


NegQ::usage = "NegQ[u] returns True if u is nonzero and has a negative form, else it returns False.";


NegQ[u_] := Not[PosQ[u]] && NeQ[u,0]


(* ::Subsubsection::Closed:: *)
(*NiceSqrtQ[u]*)


NiceSqrtQ::usage = "NiceSqrtQ[u] returns True if u has a nice squareroot (e.g. a positive number or none of the degrees of the factors of the squareroot of u are fractions), else it returns False.";


NiceSqrtQ[u_] :=
  If[RationalQ[u],
    u>0,
  Not[FractionalPowerFactorQ[Rt[u,2]]]]


(* ::Subsubsection::Closed:: *)
(*FractionalPowerFactorQ[u]*)


FractionalPowerFactorQ::usage = "FractionalPowerFactorQ[u] returns True if a factor of u is a complex constant or a fractional power; else it returns False.";


FractionalPowerFactorQ[u_] :=
  If[AtomQ[u],
    ComplexQ[u],
  If[PowerQ[u],
    FractionQ[u[[2]]],
  If[ProductQ[u],
    FractionalPowerFactorQ[First[u]] || FractionalPowerFactorQ[Rest[u]],
  False]]]


(* ::Subsection::Closed:: *)
(*Equality predicates*)


(* ::Subsubsection::Closed:: *)
(*EqQ[u, v]*)


EqQ::usage = "EqQ[u,v] returns True if u-v equals 0; else it returns False.";


EqQ[u_,v_] := Quiet[PossibleZeroQ[u-v]] || TrueQ[Refine[u==v]]


(* ::Subsubsection::Closed:: *)
(*NeQ[u, v]*)


NeQ::usage = "NeQ[u,v] returns False if u-v equals 0; else it returns True.";


NeQ[u_,v_] := Not[EqQ[u,v]]


(* ::Subsection::Closed:: *)
(*Integer inequality predicates*)


(* ::Subsubsection::Closed:: *)
(*IGtQ[u, n]*)


IGtQ::usage = "IGtQ[u,n] returns True if u is an integer and u>n; else it returns False. n must be a rational number.";


IGtQ[u_,n_] := IntegerQ[u] && u>n


(* ::Subsubsection::Closed:: *)
(*ILtQ[u, n]*)


ILtQ::usage = "ILtQ[u,n] returns True if u is an integer and u<n; else it returns False. n must be a rational number.";


ILtQ[u_,n_] := IntegerQ[u] && u<n


(* ::Subsubsection::Closed:: *)
(*IGeQ[u, n]*)


IGeQ::usage = "IGeQ[u,n] returns True if u is an integer and u>=n; else it returns False. n must be a rational number.";


IGeQ[u_,n_] := IntegerQ[u] && u>=n


(* ::Subsubsection::Closed:: *)
(*ILeQ[u, n]*)


ILeQ::usage = "ILeQ[u,n] returns True if u is an integer and u<=n; else it returns False. n must be a rational number.";


ILeQ[u_,n_] := IntegerQ[u] && u<=n


(* ::Subsection::Closed:: *)
(*Numeric inequality predicates*)


(* ::Subsubsection::Closed:: *)
(*GtQ[u, v]*)


GtQ::usage = 
"GtQ[u,v] returns True if u>v; else it returns False.
GtQ[u,v,w] returns True if u>v and v>w; else it returns False.";


GtQ[u_,v_,w_] := GtQ[u,v] && GtQ[v,w]  


GtQ[u_,v_] := 
  If[RealNumberQ[u],
    If[RealNumberQ[v],
      u>v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && u>vn]],
  With[{un=N[Together[u]]},
  If[Head[un]===Real,
    If[RealNumberQ[v],
      un>v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && un>vn]],
  False]]]


(* ::Subsubsection::Closed:: *)
(*LtQ[u, v]*)


LtQ::usage = 
"LtQ[u,v] returns True if u>v; else it returns False.
LtQ[u,v,w] returns True if u<v and v<w; else it returns False.";


LtQ[u_,v_,w_] := LtQ[u,v] && LtQ[v,w]  


LtQ[u_,v_] := 
  If[RealNumberQ[u],
    If[RealNumberQ[v],
      u<v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && u<vn]],
  With[{un=N[Together[u]]},
  If[Head[un]===Real,
    If[RealNumberQ[v],
      un<v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && un<vn]],
  False]]]


(* ::Subsubsection::Closed:: *)
(*GeQ[u, v]*)


GeQ::usage = 
"GeQ[u,v] returns True if u>v; else it returns False.
GeQ[u,v,w] returns True If u>=v and v>=w; else it returns False.";


GeQ[u_,v_,w_] := GeQ[u,v] && GeQ[v,w]  


GeQ[u_,v_] := 
  If[RealNumberQ[u],
    If[RealNumberQ[v],
      u>=v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && u>=vn]],
  With[{un=N[Together[u]]},
  If[Head[un]===Real,
    If[RealNumberQ[v],
      un>=v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && un>=vn]],
  False]]]


(* ::Subsubsection::Closed:: *)
(*GeQ[u, v]*)


LeQ::usage = 
"LeQ[u,v] returns True if u>v; else it returns False.
LeQ[u,v,w] returns True if u<=v and v<=w; else it returns False.";


LeQ[u_,v_,w_] := LeQ[u,v] && LeQ[v,w]  


LeQ[u_,v_] := 
  If[RealNumberQ[u],
    If[RealNumberQ[v],
      u<=v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && u<=vn]],
  With[{un=N[Together[u]]},
  If[Head[un]===Real,
    If[RealNumberQ[v],
      un<=v,
    With[{vn=N[Together[v]]},
    Head[vn]===Real && un<=vn]],
  False]]]


(* ::Subsubsection::Closed:: *)
(*RealNumberQ[u]*)


RealNumberQ::usage = "If u is an explicit non-complex number, RealNumberQ[u] returns True; else it returns False.";


RealNumberQ[u_] := NumberQ[u] && Head[u]=!=Complex


(* ::Section::Closed:: *)
(*2 Polynomial Routines*)


(* ::Subsection::Closed:: *)
(*PolyQ[F[x], x, n]*)


(* Mathematica's built-in PolynomialQ, Exponent and Coefficient functions can return erroneous results because they do not *)
(* cancel the gcd in pseudo-rational functions that are actually polynomial. *)
(* PolynomialQ[F[x],x] returns false, but PolynomialQ[F[x],x^2] returns True! *)
(* For some unfully expanded polynomials, the built-in Mathematica function Exponent sometimes returns erronously large degrees. *)
(* For example, Exponent[3*(1+a)*x^4 + 3*x^5 + x^6 - (a+x+x^2)^3, x] incorrectly returns 4 instead of 3. *)
(* Despite what the online help says, PolynomialQ[u,x^v] returns an error message if v is a sum. *)


PolyQ::usage = 
"PolyQ[F[x],x] returns True if F[x] is a polynomial in x; else it returns False.
PolyQ[F[x],x,n] returns True if F[x] is a polynomial in x of degree n; else it returns False.
PolyQ[F[x],x^C] returns True if C is free of x and F[x] is a polynomial in x^C; else it returns False.
PolyQ[F[x],x^C,n] returns True if C is free of x and F[x] is a polynomial in x^C of degree n; else it returns False.";


PolyQ[Fx_,x_Symbol] :=
  PolynomialQ[Fx,x] || PolynomialQ[Together[Fx],x]


PolyQ[Fx_,x_Symbol,n_] :=
  If[PolynomialQ[Fx,x],
    EqQ[Exponent[Fx,x],n] && NeQ[Coefficient[Fx,x,n],0],
  With[{Gx=Together[Fx]},
  PolynomialQ[Gx,x] && EqQ[Exponent[Gx,x],n] && NeQ[Coefficient[Gx,x,n],0]]]


PolyQ[Fx_,x_Symbol^n_Integer] :=
  If[n<=0,
    False,
  If[PolynomialQ[Fx,x],
    PolynomialQ[Fx,x^n],
  With[{Gx=Together[Fx]}, PolynomialQ[Gx,x] && PolynomialQ[Gx,x^n]]]]


PolyQ[Fx_,x_Symbol^C_] :=
  If[Fx===x,
    IGtQ[1/C,0],
  If[FreeQ[Fx,x],
    True,
  If[PowerQ[Fx],
    If[Fx[[1]]===x,
      IGtQ[Simplify[Fx[[2]]/C],0],
    IGtQ[Fx[[2]],0] && PolyQ[Fx[[1]],x^C]],
  If[ProductQ[Fx] || SumQ[Fx],
    PolyQ[First[Fx],x^C] && PolyQ[Rest[Fx],x^C],
  False]]]]


PolyQ[Fx_,x_Symbol^C_,n_] :=
  PolyQ[Fx,x^C] && EqQ[Expon[Fx,x^C],n] && NeQ[Coeff[Fx,x^C,n],0]


(* ::Subsection::Closed:: *)
(*Expon[P[x], x]*)


Expon::usage = "Expon[P[x],x] returns the degree of the polynomial P[x] in x.";


Expon[Px_,x_] := Exponent[Together[Px],x]


(* ::Subsection::Closed:: *)
(*Coeff[P[x], x, n]*)


Coeff::usage = "Coeff[P[x],x,n] returns the coefficient nth degree term of the polynomial P[x] in x.";


Coeff[Px_,x_,n_Integer] := Coefficient[Together[Px],x,n]


(* ::Subsection::Closed:: *)
(*PolyQuo[P[x], Q[x], x]*)


PolyQuo::usage = "P[x] and Q[x] are polynomials in x.  PolyQuo[P[x],Q[x],x] returns the quotient of P[x] divided by Q[x] over a commonn denominator, with the remainder dropped.";


PolyQuo[Px_,Qx_,x_Symbol] :=
  With[{Rx=Together[PolynomialQuotient[Px,Qx,x]]},
  ExpandToSum[Numerator[Rx],x]/Denominator[Rx]]


(* ::Subsection::Closed:: *)
(*PolyRem[P[x], Q[x], x]*)


PolyRem::usage = "P[x] and Q[x] are polynomials in x.  PolyRem[P[x],Q[x],x] returns the remainder of P[x] divided by Q[x] over a commonn denominator.";


PolyRem[Px_,Qx_,x_Symbol] :=
With[{Rx=Together[PolynomialRemainder[Px,Qx,x]]},
  ExpandToSum[Numerator[Rx],x]/Denominator[Rx]]


(* ::Section::Closed:: *)
(*3 Miscellaneous Routines*)


(* ::Subsection::Closed:: *)
(*IntPart[u]*)


IntPart::usage = "IntPart[u] returns the sum of the integer terms of u.";


IntPart[m_*u_,n_:1] :=
  IntPart[u,m*n] /;
RationalQ[m]


IntPart[u_,n_:1] :=
  If[RationalQ[u],
    IntegerPart[n*u],
  If[SumQ[u],
    Map[Function[IntPart[#,n]],u],
  0]]


(* ::Subsection::Closed:: *)
(*FracPart[u]*)


FracPart::usage = "FracPart[u] returns the sum of the non-integer terms of u.";


FracPart[m_*u_,n_:1] :=
  FracPart[u,m*n] /;
RationalQ[m]


FracPart[u_,n_:1] :=
  If[RationalQ[u],
    FractionalPart[n*u],
  If[SumQ[u],
    Map[Function[FracPart[#,n]],u],
  n*u]]


(* ::Subsection::Closed:: *)
(*Rt[u, n]*)


Rt::usage = "Rt[u,n] returns the simplest nth root of u.";


Rt[u_,n_Integer] := RtAux[Together[Simplify[Together[u]]],n]


RtAux[u_,n_] :=
  If[PowerQ[u],
    u[[1]]^(u[[2]]/n),
  If[ProductQ[u],
    Map[Function[RtAux[#,n]],u],
  If[OddQ[n] && LtQ[u,0],
    -RtAux[-u,n],
  u^(1/n)]]]


(* ::Subsection::Closed:: *)
(*Star[u, v]*)


Star::usage = "Star[u,v] displays as u*v, and returns the product of u and v with u distributed over the terms of v.";


Star[u_,v_] := 
  If[AtomQ[v],
    u*v,
  If[SumQ[v],
    Map[Function[Star[u,#]],v],
  If[Head[v]===Star,
    Star[u*v[[1]],v[[2]]],
  u*v]]]


(* ::Subsection::Closed:: *)
(*Subst[F[x], x, v]*)


Subst::usage = "Subst[F[x],x,v] returns F[x] with all x's replaced by v.";


Subst[Fx_,x_Symbol,v_] :=
  If[AtomQ[Fx],
    If[EqQ[Fx,x],
      v,
    Fx],
  If[EqQ[Head[Fx],Int] || EqQ[Head[Head[Fx]],Defer],
    Defer[Subst][Fx,x,v],
  Map[Function[Subst[#,x,v]],Fx]]]


(* ::Subsection::Closed:: *)
(*ExpandToSum[F[x], x]*)


Subst::usage = "ExpandToSum[F[x],x] returns F[x] expanded into a sum of monomials of x.";


ExpandToSum[Fx_,x_Symbol] :=
  If[PolynomialQ[Fx,x],
    Apply[Plus,Map[Function[Simplify[Coefficient[Fx,x,#]]*x^#], Exponent[Fx,x,List]]],
  Expand[Fx,x]]

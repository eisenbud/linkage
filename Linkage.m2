-*newPackage(
    "Linkage",
    Version => "0.1",
    Date => "",
    Headline => "",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    Keywords => {""},
    AuxiliaryFiles => false,
    PackageExports => {
"MonomialOrbits"
"DGAlgebras"
"LocalRings"
"AInfinity"
"CompleteIntersectionResolutions"},
DebuggingMode => false
    )

export {}
*-
-* Code section *-


-* Documentation section *-
-*beginDocumentation()

doc ///
Key
  Linkage
Headline
Description
  Text
  Tree
  Example
  CannedExample
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///

-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///
-*
end--

-* Development section *-
-*restart
debug needsPackage "Linkage"
check "Linkage"

uninstallPackage "Linkage"
restart
installPackage "Linkage"
viewHelp "Linkage"
*-

-*
Basic questions:
in codim 3:

licci monomial ideals decrease sum bettis monotonically on double links (m-primary). (Yes, m-primary, maybe)

do licci general ideals have plateaus of at most 2 with respect to general links -- no (Weyman et al)=

is homogeneous licci == licci? -- is there a homogeneous algorithm to determine licci?
DE: write test for "homogeneous improvement", or, better homogeneous licci.(homogenization technique in H-U?)

know that if a general link decreases sum bettis, then there is 
a homogeneous link that does the same.??

Is it true that if the codim of the mixed part is >= 2 then
--HU prove it is not licci. 

In all the examples (monomial primary 4,5 variables) we've seen, 
the conjecture: (g-1) max gen degrees < min last shift => licci
holds.
*-

--needsPackage "StableResidual"
needsPackage "MonomialOrbits"
needsPackage "DGAlgebras"
needsPackage "LocalRings"
needsPackage "AInfinity"
needsPackage "CompleteIntersectionResolutions"
needsPackage"Isomorphism"

-*
Conditions implied by licci: R= S/I (S RLR)
g := grade
1. Strongly CM (SCM and generically CI -> Sym^2I = I^2) (Huneke) (if g>=2, then SCM is equiv to depth Z_i(Koszul) \geq dim R+2.
2. Ext_S^i(R,R) is CM for i = 1..grade R - 1 (proved by Buchweitz) -- and depths of these are linkage invariants (B+Ulrich). But
Ext^j_R(Ext_S^i(R,R),omega_R) is invariant for j>0$.
3. In the artin case, degree (I**\omega_R) = (grade I) * degree R (if R is smoothable by H-U; with that, 2=> 3) 
4. shift: max last shift > (grade -1) min first shift (Huneke-Ulrich)
5. for an m-primary monomial ideal:
   licci iff:  the the mixed monomials have grade 1 , and this remains after linkage with the pure powers

Conjectures:
A. replace max by min in 4 and reverse inequality, then licci
B. linear strand cannot go to end in grade >= 3. 
C. max (grade -i)-th shift > (grade -i -1)min(first shift), for i \leq grade -2
D. If I is licci and 0-dimensional, then m^s\subset I => mu(I)< s+grade I. Proven for monomial, g = 2, s<=3.

Questions:
a. 5 for some other ideals containing pure powers. Perhaps easier: if I is primary = squares + codim 2, does that imply NOT licci
or even low regularity, as in the monomial case?

b. In the monomial case, is there a strengthening of 4 using the multi-grading?
(And do the counterexamples to licci is a betti condition go away?)

Construction: start with I a licci gen ci; J = geometric link; then I+J is gor and licci (of grade = grade I +1).
*-
omega = I -> (
    c:=codim I;
    Ext^c((ring I)^1/I, (ring I)^1)
    )

isGenericallyCI = I -> (
    P := presentation module (I' = trim I);
    c := codim I';
    n := numgens I';
    c<codim minors (n-c, P))

isStronglyCM = method()
isStronglyCM Ideal := Boolean => I' -> (
    I :=trim I';
    n := numgens I;
    g := codim I;
    if g<2 then error"expected ideal of grade >= 2";
    K := koszul(gens I);
    for i from 1 to n-g list (
	if pdim image K.dd_i>g-1 then return false);
    true)
isStronglyCM Ring := R -> isStronglyCM ideal R

isExtCM = method()
isExtCM Ideal := Boolean => I' -> (
    --Licci implies Ext^i(R,R) is CM for all i
    --proven by Buchweitz (unpublished by B-Ulrich)
    I :=trim I';
    R := (ring I)^1/I;
    g := codim I;
    if pdim R > g then return false;
    for i from 1 to g-1 do (
	if pdim Ext^i(R,R) > g then return false);
    true)
isExtCM Ring := R -> isExtCM ideal R


--In the artin case, 
--degree Ext^i(R,R) = binomial(grade I,i) * degree R 

isDegExtLicciLike = method()
isDegExtLicciLike Ideal := List => I' -> (
    --Licci implies Ext^i(R,R) is CM for all i
    --proven by Buchweitz (unpublished by B-Ulrich)
    I :=trim I';
    R := (ring I)^1/I;
    g := codim I;
    if g < dim ring I then error "expect 0 dimensional input";
        dif :=for i from 1 to g//2 list
	    	 degree Ext^i(R,R) - binomial(g,i) * degree R;
	        return dif)
-*
*-
isDegExtLicciLike Ring := o-> R -> isDegExtLicciLike ideal R

///
restart
load "Linkage.m2"
///
--max last shift > (grade -1) min first shift (Huneke-Ulrich)

isShiftLicciLike = method(Options => {Sufficient => false})
isShiftLicciLike Ideal := Boolean => o -> I -> (
    B := keys minimalBetti I;
    pd := max (B/first);
    if pd != codim I then return "I is not perfect";
--    Bmax := select(B, k -> first k == pd);
    maxTwists := for i from 0 to pd list(
	Btemp := select(B, k->first k == i);
	 max apply(Btemp, k-> last k)
	);
    Bmax := select(B, k -> first k == pd);    
  --  maxLastTwist := max(Bmax/last);
    minLastTwist := min(Bmax/last);
    B1 := select(B,k-> first k == 1);
    minFirstTwist := min (B1/last);
    maxFirstTwist := max (B1/last);    
    if o.Sufficient === false then
    all(pd-2, i-> maxTwists_(i+3) > (i+2)*minFirstTwist) else
    minLastTwist > (pd-1)*maxFirstTwist
    )
hu = I -> (
    --separate the generators of a monomial ideal
    --into those that are pure powers and those that
    --are not, as in the paper of Huneke and Ulrich
    --on licci monomial ideals.
    S := ring I;
    P := (i,j) -> matrix{{S_i*S_j}};
    Ilist := flatten for i from 0 to #gens S -2 list 
        for j from i+1 to #gens S -1 list 
	  ideal (entries(S_i*S_j* contract(P(i,j), gens I)))_0;
    mix := trim sum Ilist;
    powers := ideal compress (gens I % mix);
    (powers, mix)
    )

pureAndMixed = method()
pureAndMixed Ideal := List => I' -> (
    I := trim I';
    pures := select(I_*, i -> #support i == 1);
    mixes := select(I_*, i -> #support i > 1);
    if mixes == {} then mixes = {0_(ring I')};
   (ideal pures, ideal mixes)
  )

monomialLink = I -> (
    (pure, mix) := pureAndMixed I;--hu I;
    pure: mix)

reducedForm= method()
reducedForm Ideal := Ideal => I' ->(
    --double link
    I := monomialIdeal I';
    while true do(
    (pure,mix) := pureAndMixed I;
    if codim mix >1 or mix == 0 then return I else
    I = I:gcd mix_*))


///
restart
kk = ZZ/101
T = kk[a,b,c]
I = ideal"a2b,abc3 "
I = monomialIdeal(a^4,b^4,a*b^2*c,b^3*c,a^2*c^2,a*b*c^2,b^2*c^2,a*c^3,b*c^3,c^4)
(p,m) = pureAndMixed I

gcd m_*
weakPolarization I
I
isLicciMonomialIdeal I
pureAndMixed I
///

weakPolarization = method(Options => {"AllVars" => false, VariableName => X})
weakPolarization Ideal := o -> I ->(
    I' := if class I === Ideal then monomialIdeal I else I;
    G0 := gens ring I';
    n := #G0;
    if o#"AllVars" == true then
    G1 := G0|toList(X_0..X_(#G0 -1))
                           else G1 = append(G0, X_0);
    S' := coefficientRing ring I [G1];
    J := polarize I';
    R := ring J;
    V := gens R;
    if o#"AllVars" == true then
    phi := map(S',R,apply(V,
	    v -> S'_((baseName v)#1#0)+
	    S'_(n+(baseName v)#1#0)*(baseName v)#1#1))
                           else
    phi = map(S',R,apply(V,
	    v -> S'_((baseName v)#1#0)+
	    S'_n*(baseName v)#1#1));
    phi J
    )

isPurePower = m -> (
    M = ideal m;
    G = gens ring m;
    L = for x in G list saturate(M,x);
    #select(L, ell-> ell==M) == #G -1)

commonPolarization = (I1,I2) ->(
    S = ring I1;
    if not S === ring I2 then error"ideals should be from same ring";
    L1 = flatten (exponents \ for m in I1_* list  m);
    L2 :=flatten( exponents \ for m in I2_* list  m);
    exps := apply(numgens ring I1, i-> for ell in L1|L2 list ell_i);
    maxes := exps/max;
    R = ring polarize(
    (monomialIdeal product apply(numgens S, i -> S_i^(maxes_i))));
    I1' := monomialIdeal sub(polarize I1, R);
    I2' := monomialIdeal sub(polarize I2, R);
    (I1',I2')
    )


test=(P1,P2) ->(
   --assume:
   --licci's are eliminated;
   --P1,P2 in reduced form;
   --P1 !=P2
(I1,I2) :=  commonPolarization(P1,P2);
R:= ring I1;
n := numgens R;
omega1 := omega I1;
omega2 := omega I2;
EE1 := for k from 4 to n list Ext^k((module I1)**omega1, R^1);
EE2 := for k from 4 to n list Ext^k((module I2)**omega2, R^1);
EE1' := for k from 4 to n list Ext^k(Hom(module I1,R^1/I1), R^1);
EE2' := for k from 4 to n list Ext^k(Hom(module I2,R^1/I2), R^1);
({apply (n-3,i->isIsomorphic(EE1_i,EE2_i))},
{apply (n-3,i->isIsomorphic(EE1'_i,EE2'_i))})
)

koszulHomologyTest = (P1,P2) ->(
    (I1,I2) :=  commonPolarization(P1,P2);
    R:= ring I1;
    n := numgens R;
    H1 := HH_1 koszul gens I1;
    H2 := HH_1 koszul gens I2;
    EH1 := for i from 5 to n list Ext^i(H1, R^1);
    EH2 := for i from 5 to n list Ext^i(H2, R^1);    
    apply (n-4,i->isIsomorphic(EH1_i,EH2_i))
    )
linkedKoszulHomologyTest = (P1,P2) ->
      koszulHomologyTest(P1,monomialLink1 P2)

monomialLink1 = I -> (
    purePowers = ideal for m in I_* list
                 if isPurePower m then m else continue;
    purePowers:I)
    
    

///
S = ZZ/101[a,b,c]
m = a^4*b
I1 = monomialIdeal (a^4*b)
I2 = monomialIdeal"abc"
commonPolarization (I1,I2)

///
TEST///
--monomial ideals where licci is NOT determined by betti
restart
load "Linkage.m2"
--example of Boocher
kk = ZZ/101
S = kk[a,b,c, Degrees => {{1,0,0}, {0,1,0}, {0,0,1}}]
I0 = monomialIdeal"a3,b3,c3"
weakPolarization (I0, "AllVars" => false)

I1 = ideal"bc2, a2bc, a2b2"
I2 = ideal"bc2, a2c2, a2b2"
J1 = I0+I1
J2 = I0+I2
isDegExtLicciLike J1
isDegExtLicciLike J2
betti res J1 == betti res J2
isLicciMonomialIdeal J1 == true
isLicciMonomialIdeal J2
F1 = res J1;F2 = res J2;
netList{degrees F1_1,degrees F1_3}
--example of Mantero et al
kk = ZZ/101
S = kk[w,x,y,z]
I0 = ideal"w3,x3, y3,z3"
I2 = ideal"w2x,w2y, wxz"
I1 = ideal"w2x, wx2,wy2"
J1 = I0+I1
J2 = I0+I2
isDegExtLicciLike J1
isDegExtLicciLike J2
betti res J1
betti res J2
isLicciMonomialIdeal J1 == true
isLicciMonomialIdeal J2
F1 = res J1;F2 = res J2;
netList{degrees F1_1,degrees F1_3}


restart
load "Linkage.m2"

S = ZZ/101 [a..d]
I3 = minors(2, matrix"a,b,c;b,c,d")
I3' = ideal"a4, d3"+minors(2, matrix"a,b,c;b,c,d")
I4 = minors(2, matrix"a,b,c,d;b,c,d,a")

I = I4

assert (isShiftLicciLike I3' == true)
assert (isShiftLicciLike I4 == false)
assert(isDegExtLicciLike I3' == true)

assert(isStronglyCM I3 == true)
assert(isStronglyCM I4 == false)
assert(isStronglyCM (S/I4) == false)

assert(isExtCM I3 == true)
assert(isExtCM (S/ I4) == false)

S = ZZ/101 [a..c]
I = ideal"a2, ab, ac, b2c+bc2, c4,bc3,b2c2, b4"
assert(isDegExtLicciLike I == false)


///

    
///

restart
load "Linkage.m2"


S = ZZ/101[x,y,z]
I = ideal"x3,y4,z5,xy,xz"
I = ideal"x3,y4,z2,xy, yz,xz"
isLicciMonomialIdeal I
isLicciMonomialIdeal ideal (x^3,y^2,z^2,x*y*z)


I1 = ideal"x2,y3,z4,y,z"

I = (ideal vars S)^2
isLicci I
d = 6
I0 = ideal apply(gens S, x -> x^d)
I = I0+ideal"xyz"*ideal"xy,xz,yz"
isLicci I
monomialLink I


betti res I
(pure, mix) = hu I
I' = pure:mix
betti res I'
isLicci I
betti res I
(pure, mix) = hu I'
I'' = pure:mix
betti res I''

///

isLicci1 = I -> (
    -- Huneke-Ulrich test for Licci; return
    -- either true, or else false and a Golod linked
    -- monomial ideal. Print any stage with codim 2 mixed part.
    --if sumBettis stays constant stop
    S := ring I;

    if I == ideal(1_S) then return "Unit";
    t := testGolod I;
    if t then (
	<<I<<minBetti I<<" is Golod."<<endl;
	return false);
    I' := I;
    s := sumBettis I';
    s' := s;
    <<s<<", ";
    if s<= 8 then (<<endl; return "Licci");
    (pure,mix) := hu I';
    if codim mix > 1 then (<<endl <<toString primaryDecomposition mix <<endl);
    --I' := trim (pure:mix);

    while not t and not (s <= 8)  do(
        I' = trim (pure:mix);
	s = sumBettis I';
	<<s<<", ";
	if s' == s then 
	    (<< endl<< "sumBettis " << toString I << " does not strictly decrease."; return());
	t = testGolod I';
	s' = s;
	--if I' == ideal(1_S) then (<<endl; return true);
	(pure,mix) = hu I';
	if I' == pure then (<<endl; return true);

	if codim mix > 1 then (<<endl <<toString primaryDecomposition mix <<endl);
	    );
	
    if t then (
       <<I<<minBetti I<<" is Golod."<<endl;
       return false) else (<<endl; return "Licci"))

--example from Huneke-Migliore-Nagel-Ulrich of an ideal that is homogeneous licci 
--but not minimally homog licci
exampleHMNU = method()
exampleHMNU Ring := S -> (
    --must be a polynomial ring in 3 vars x,y,z
    use S;
    ideal"x2y+y3-yz2- z3, xy2-xz2, x3z-xyz2, y2z2-z4, x6, z6, xz5")
///
restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
I = exampleHMNU(S)
R = ring I
cvwh1 I
--cvw I --too slow
///


--two examples of families of ideals of Betti numbers 1,5,6,2; They are
--licci AND (as one sees from the Betti table) Golod.
x = symbol x
exampleCLKW = method()
exampleCLKW Ring := kk  -> (
R := kk[x_12,x_13,x_14,x_23,x_24,x_34,y_12,y_13,y_14,y_23,y_24,y_34,z_123,z_124,z_134,z_234];
M := matrix{{x_12,x_13,x_14,x_23,x_24,x_34},{y_12,y_13,y_14,y_23,y_24,y_34}};
l1 := det(M^{0,1}_{4,1})-det(M^{0,1}_{2,3})-det(M^{0,1}_{5,0});
l2 := det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})-det(M^{0,1}_{5,0});
l3 := -det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})+det(M^{0,1}_{5,0});
l4 := det(M^{0,1}_{1,4})-det(M^{0,1}_{2,3})-det(M^{0,1}_{0,5});
q1 := z_123*l1+2*z_124*(det(M^{0,1}_{1,3}))-2*z_134*det(M^{0,1}_{0,3})+2*z_234*det(M^{0,1}_{0,1});
q2 := -2*z_123*(det(M^{0,1}_{2,4}))+z_124*l2-2*z_134*det(M^{0,1}_{0,4})+2*z_234*det(M^{0,1}_{0,2});
q3 := -2*z_123*det(M^{0,1}_{2,5})+2*z_124*det(M^{0,1}_{1,5})+z_134*l3+2*z_234*det(M^{0,1}_{1,2});
q4 := -2*z_123*det(M^{0,1}_{4,5})+2*z_124*det(M^{0,1}_{3,5})-2*z_134*det(M^{0,1}_{3,4})+z_234*l4;
a := x_12*x_34-x_13*x_24+x_14*x_23;
b := x_12*y_34-x_13*y_24+x_14*y_23+x_34*y_12-x_24*y_13+x_23*y_14;
c := y_12*y_34-y_13*y_24+y_14*y_23;
u := b^2-4*a*c;
ideal(q1,q2,q3,q4,u))

------------------------------------------------------------------------------------------------- Deformed ideal J(t)
exampleCLKW' = method()
exampleCLKW' Ring := kk -> (
R := kk[x_12,x_13,x_14,x_23,x_24,x_34,y_12,y_13,y_14,y_23,y_24,y_34,z_123,z_124,z_134,z_234,t];
M := matrix{{x_12,x_13,x_14,x_23,x_24,x_34},{y_12,y_13,y_14,y_23,y_24,y_34}};
l1 := det(M^{0,1}_{4,1})-det(M^{0,1}_{2,3})-det(M^{0,1}_{5,0});
l2 := det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})-det(M^{0,1}_{5,0});
l3 := -det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})+det(M^{0,1}_{5,0});
l4 := det(M^{0,1}_{1,4})-det(M^{0,1}_{2,3})-det(M^{0,1}_{0,5});
q1 := z_123*l1+2*z_124*(det(M^{0,1}_{1,3}))-2*z_134*det(M^{0,1}_{0,3})+2*z_234*det(M^{0,1}_{0,1});
q2 := -2*z_123*(det(M^{0,1}_{2,4}))+z_124*l2-2*z_134*det(M^{0,1}_{0,4})+2*z_234*det(M^{0,1}_{0,2});
q3 := -2*z_123*det(M^{0,1}_{2,5})+2*z_124*det(M^{0,1}_{1,5})+z_134*l3+2*z_234*det(M^{0,1}_{1,2});
q4 := -2*z_123*det(M^{0,1}_{4,5})+2*z_124*det(M^{0,1}_{3,5})-2*z_134*det(M^{0,1}_{3,4})+z_234*l4;
a := x_12*x_34-x_13*x_24+x_14*x_23;
b := x_12*y_34-x_13*y_24+x_14*y_23+x_34*y_12-x_24*y_13+x_23*y_14;
c := y_12*y_34-y_13*y_24+y_14*y_23;
u := b^2-4*a*c;
ideal(q1-z_123*t,q2-z_124*t,q3-z_134*t,q4-z_234*t,u-t^2)
)  -------deformed ideal J(t)
-----

-- Christensen, Veliche, and Weyman (Linkage classes of grade 3 perfect ideals, Thm 3.7) prove:
-- cvw: If a CM ring R of codim 3 is not Golod 
-- then either p := rank tor_1(R,k)^2 or q := rank tor_1*tor_2 is nonzero.
-- If p>0 then a general link has small betti sum. If p = 0 but q>0 then
-- the general link has the same betti sum, but also has p>0, so
-- the second general link has smaller betti sum.
-- This process leads either to a complete intersection or a Golod ring.

generalLink = J -> (
    J = if class J === Ideal then J else ideal J;
    if J == ideal(1_(ring J)) then return J;
    S:= ring J;
    J0 := ideal (gens(J)*random(S^(rank source gens J), S^(codim J)));
    elapsedTime K := J0:J;
    elapsedTime J' := if isHomogeneous K then K else localTrim K
)
pregeneralLink = J -> (
    --give return a general regular sequence and the original ideal.
    --(convert from a matrix to an ideal if necessary)
    J = if class J === Ideal then J else ideal J;
    if J == ideal(1_(ring J)) then return J;
    S:= ring J;
    J0 := ideal (gens(J)*random(S^(rank source gens J), S^(codim J)));
    (J0,J)
)

doubleLink = J -> generalLink generalLink J

minHomogLink = J -> (
    --finds a random homogeneous maximal regular sequence in J of minimal
    --degree, and returns the link of J with respect to this sequence.
    S := ring J;
    if J == ideal(1_S) then return J;
    genlist := J_*;
    deglist :=  sort unique (genlist/(g -> (degree g)_0));
    D := #deglist;
    II := apply(deglist, d -> ideal select(genlist, g -> (degree g)_0 <= d));
    codims := apply(II, I -> codim I);
    levels := apply(D, i -> gens II_i * matrix basis(deglist_i, II_i));
    regseq := levels_0 * random(source levels_0, S^{codims_0:-deglist_0});
    for i from 1 to D-1 do(
	regseq = regseq | 
	         levels_i * random(source levels_i, S^{codims_i-codims_(i-1):-deglist_i}));
    regs = ideal regseq;
    assert (isHomogeneous regs);
    assert (codim regs == codims_(D-1));
    (ideal regseq):J
    )

///
restart
load "Linkage.m2"
S = ZZ/101[x,y,z]
J = ideal"x2,xy,y3,z4"
minHomogLink J
///
    
minBetti = I -> (
    --this seems to be the fastest way to compute the (total) minimal betti numbers
    --for the local resolution, at the maximal ideal of variables, of an ideal,
    --in the inhomogeneous case.
    F = res I; -- nonminimal res
    S := ring I;
    kk := coefficientRing S;
    redd = map(kk, S, {numgens S:0});
    Fbar = redd F;
    H := prune HH Fbar;
    apply(#H, i-> rank H_i)
    )

sumBettis = J ->(
    if isHomogeneous J then (G := res trim J;
	                     sum(1+length G, i-> rank G_i))
    else
       sum minBetti J
    )

cvw = method()
--Christensen-Veliche-Weyman showed that every codimension 3 perfect
--ideal is linked to either a complete intersection or a Golod ideal.
--This routine makes a series of general links until the sum of the 
--Betti numbers stops changing; at that point the linked ideal is either
--the unit ideal or Golod.
cvw Ideal := Ideal => I ->(
    if I == ideal(1_(ring I)) then return I;
    I1 := I;
    s := sumBettis I1;
    J2 := generalLink (J1 := generalLink I);
    t1 := sumBettis J1;
    t2 := sumBettis J2;
    <<(s,t1,t2)<<flush<<endl;
    while s > t2 do(
      I1 = J2;
      J2 = generalLink (J1 = generalLink I1);
      s = t2;
      t1 = sumBettis J1;
      t2 = sumBettis J2;
      <<(s,t1,t2)<<flush<<endl);
      
      if t2 == 0 or J2 == ideal(1_(ring I)) then <<"Licci"<<endl<<endl else
      if isGolod (ring J2/J2) then(<<"Golod"<<endl<<J2<< endl<<endl) else J2
  )

cvwh = method()
cvwh Ideal := Ideal => I ->(
    --assumes I is homogeneous, does minimal homogeneous links
    if I == ideal(1_(ring I)) then return I;    
    I1 := I;
    s := sumBettis I1;

    J2 := minHomogLink (J1 := minHomogLink I);
    t1 := sumBettis J1;
    t2 := sumBettis J2;
    <<(s,t1,t2)<<flush<<endl;
    while s > t2 do(
      I1 = J2;
      J2 = minHomogLink (J1 = minHomogLink I1);
      s = t2;
      t1 = sumBettis J1;
      t2 = sumBettis J2;
      <<(s,t1,t2)<<flush<<endl);
      
      if t2 == 0 or J2 == ideal(1_(ring I)) then <<"Licci"<<endl<<endl else
      if isGolod (ring J2/J2) then(<<"Golod"<<endl<<trim J2<< endl<<endl) else trim J2
  )

--      /Applications/Macaulay2-1.16.99/share/Macaulay2/CompleteIntersectionResolutions.m2:1405:44-1426:6: --source code:
      
      exteriorTorModule(Matrix, ChainComplex) := (f,F) -> (
	   --Here F is a possibly nonminimal resolution of a possibly inhomogeneous module M
           --f is a matrix with entries that are homotopic to zero on F
	   --The script returns T = Tor_S(M,k) as a module over E = \wedge k**(source f):
           --In the inhomogeneous case F may not be minimal,
	   --so we cannot assume that T = k**F.
           S := ring F;
	   n := numgens S;
           k := coefficientRing S;     
	   redd := map(k,S,{n:0},DegreeMap=>d->{});	   
    	 --ring over which the Tor module will be defined
	   e := symbol e;
           E := k[e_0..e_(numcols f -1), SkewCommutative => true];
	   toE := map(E, k);

	   kF := redd F; -- this is not yet tor; we must construct the homology HH_(kF)
    	   skF := apply(3+length kF, i-> syz kF.dd_(i));
	   dbar := apply(3+length kF, i -> kF.dd_i//skF_(i-1));
	 --Now HH_i(kF) == coker dbar_(i+1) == source skF_i/image(dbar_(i+1))
    	   
	 --create the homotopies representing the action of E, first on F, then on kF  
           H := makeHomotopies1(f,F);
           goodkeys := select(keys H, k->k_1>=0);	   
	   Hk0 := hashTable apply(goodkeys, h-> (h, redd H#h));

	 --we now transfer the action of the homotopies H to the pruned homology modules:
    	 --Hk#{j,i} is to be the homotopy for the j-th generator from HH_i to HH_(i+1)
           Hk := hashTable apply(goodkeys, ke-> ke =>
	             inducedMap (coker dbar_(ke_1+2), coker dbar_(ke_1+1), 
			          map(coker dbar_(ke_1+2), source skF_(ke_1),(Hk0#ke*skF_(ke_1))//skF_(ke_1+1))
				  )
			      );

         --replace with the pruned version pHk
	   T := hashTable apply(toList(0..1+length F), i -> 
	           i => if i<= length F then prune source Hk#{0,i} else prune k^0);
	   p := apply(toList(0..1+length F), i-> (T#i.cache.pruningMap));
	   pHk := hashTable(apply(keys Hk, ke -> 
		   ke => ((p_(ke_1+1))^(-1))*Hk#ke *p_(ke_1)
	       ));
    	   
	 --now move Hk and T to E
           HkE := hashTable apply(keys pHk, ke-> ke => toE pHk#ke);
    	   TE = hashTable apply(keys T, ke -> ke => E^{-ke}**toE T#ke);

           makeModule(TE, vars E, HkE)
      )

basicKoszulSyzygies = method()
basicKoszulSyzygies Ideal := Module => I -> (
    --summodule of exteriorTorModule generated by 1; image of the Koszul complex
    --of the generators of I in the homology of the resolution of I tensored with 
    --the residue field.
S := ring I;
if I == ideal(1_S) then return"input is the unit ideal";
T := exteriorTorModule(gens I, res I);
E := ring T;
BK := prune image map(T, E^1,T_{0});
s := hf(0..numgens S, BK);
t := hf(0..numgens S, T);
<<s<<" "<<t<<" "<<sum t<<flush<<endl;
BK
)

--Long's test for Golod in monomial ideals in 3 vars; conjecture for all ideals 
--(1) [I : x1] · [I : (x2, x3)] ⊆ I for all permutations {x1, x2, x3} of {x, y, z}.
--(2) [I : x1] · [I : x2] ⊆ x3[I : (x1, x2)] + I for all permutations {x1, x2, x3} of {x, y, z}.

--this shows: no 5 generator Golod monomial ideals (any fin length golod in 3 vars that contains
--x^a,y^b also contains x^(a-1)y^(b-1), and permutations -- two more gens aren't enough.
testGolod = I -> (
    P := {{0,1,2},{1,2,0},{2,0,1}};
    G := gens ring I;    
    t1 := all(3, i-> (
	    g = G_(P_i);
    gens((I:ideal g_0)*(I:ideal(g_1,g_2)))%I == 0
    and
    gens((I:ideal g_0)*(I:ideal g_1))%(g_2*(I:ideal(g_0,g_1))+I) == 0
))
)




///
S = ZZ/101[x,y,z]
I = (ideal vars S)^2
testGolod I
testGolod1 I
///

regularProducts = I -> (mm := ((S^1/M)**extend(res I, koszul gens I0, matrix{{1_S}}));
    mm_2 == 0)

localTrim = I -> (
    S := ring I;
    if not S.?maxIdeal then setMaxIdeal ideal vars S;
    ideal localMingens gens I)



rand = method(Options => {Check =>true})
rand(ZZ, Ideal) := Ideal => o -> (d,I) ->  ideal (gens I * random(source gens I, (ring I)^{-d}))
rand(ZZ, Ideal, Ideal) := Ideal => o -> (d,I,J) ->  (

    I' := ideal(gens I % J);
    rand(d, I')
    )

rand(List, Ideal) := Ideal => o-> (L,I) ->(
    L' = sort L;
    g := rand (L'_0,I);
    apply(#L'-1, i -> g = rand(L'_(i+1), I,g) + g);
    if (o.Check == true and codim g<#L) then return "failed" else return g)

combs = degs -> unique flatten (
         for i from 0 to #degs - 3 list 
           flatten for j from i+1 to #degs - 2 list
	      for k from j+1 to #degs -1 list
	        {degs_i, degs_j, degs_k})

suitableDegrees = I -> (
    C := combs sort flatten degrees I;
    L := for co in C list (
	(co, rand(co, I, Check => true)));
    select(L, ell -> ell_1 =!= "failed")
    )

///
restart
load "Linkage.m2"
S = ZZ/101[x,y,z]
I = ideal"x3,y4,z5,xy,xz"
netList suitableDegrees I
rand({2,2,3}, I, Check => true)
///
generalHomogeneousLinkage = method()
generalHomogeneousLinkage(List, Ideal) := Ideal => (D,I) -> (
    --I should be a homogeneous ideal, D a list of codim I degrees 
    --(eg the degrees of minimal generators of I).
    --Form the link with respect to general homogeneous elements of I 
    --of degrees D
    D' := sort D;
    g := rand(D',I);
    if g === "failed" then return "failed";
    g:I)


-*bestHomogLink = I -> (
    C := combs sort flatten degrees I;
    elapsedTime A := for co in C list(
	I1 := generalHomogeneousLinkage(co,I);
	if I1 === "failed" then ((<<co<<", "); continue) else
	(I1, sumBettis I1));
    <<A<<endl;
    m := min(A/last);
    p := positions(A, a-> last a == m);
    <<C_p<<endl;
    apply (A_p, pa -> first pa)
    )
*-

bestHomogLink = I -> (
    su := suitableDegrees I;
    A := for s in su list(
	I1 := s_1:I;
	(I1, sumBettis I1));
    m := min (A/last);
    p := first positions(A, a-> last a == m);
    A_p
    )

cvwh1 = I ->(
    <<(s := sumBettis I)<<" ,";
    I1 := bestHomogLink I;
    <<(s1 := I1_1)<<" ,";
    J := bestHomogLink I1_0;
    <<(s2 := J_1)<<" ,";
    while s2>8 and s2<s do(
	<< (s = s2) <<" ,";
        I1 = bestHomogLink J_0;
        << (s1 = I1_1)<<" ,";
        J = bestHomogLink I1_0;
        s2 = J_1);
        if s2<=8 then <<s2<<", ";
    if s>8 and s == s2 then (
	t := isGolod (ring I/J_0);
	if t then return "Golod" else return J_0);
    )

///
restart
load "Linkage.m2"
J = exampleCLKW (ZZ/32003);
--J' = exampleCLKW' (ZZ/32003);
--minimalBetti J'
R = ring J
S = ZZ/32003[x,y,z]
Jbar = (map(S,R,random(S^1,S^{16:-1}))) J;
minimalBetti Jbar
isGolod(S/Jbar)
cvwh1 Jbar
D = {3,3,3}
I = generalHomogeneousLinkage(D,Jbar)
degrees I
betti res Jbar
betti res I
I1 = generalHomogeneousLinkage({2,2,3},I)
betti res I1
///
end--

--Ulrich licci Golod example
restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
I = ideal"x3+xz2, y3+yz2, z3,xyz,x4+y4-x2y2"
minimalBetti I
assert(isGolod(S/I)==true)
use S
J = ideal"x3+xz2, y3+yz2, z3"
I' = J:I
assert(isGolod(S/I') == false)
I'' = generalLink I'
sumBettis I
sumBettis I'
sumBettis I''
elapsedTime cvwh1 I
isLicci I
I = generalLink I

restart
load "Linkage.m2"
J = exampleCLKW (ZZ/32003);
R = ring J
S = ZZ/32003[x,y,z]
Jbar = (map(S,R,random(S^1,S^{16:-1}))) J;
cvwh1 Jbar

basicKoszulSyzygies Jbar
cvw Jbar
codim Jbar
betti res Jbar
I = generalLink Jbar
minBetti I
I = generalLink I
minBetti I

I = minHomogLink Jbar
betti res I
I = minHomogLink I
betti res I

-------------Huneke-Miglore-Nagel-Ulrich example
restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
I = exampleHMNU S
elapsedTime cvwh1 I

sumBettis I
elapsedTime I1 = bestHomogLink I
sumBettis I1_0


C_0
apply(#C, try (I1 = generalHomogeneousLinkage (C_0,I)) then I1 else continue)


u = unique degs
mults = apply(u, d -> (d, #positions(degs, de -> de == d)))
betti res rand({3,4,6},I)

I1 = generalHomogeneousLinkage({3,4,6},I)
minimalBetti I1
sumBettis I
sumBettis I1
degrees I1

I2 = generalHomogeneousLinkage({3,4,5},I1)
sumBettis I2
degrees I2

Note:
I5' = generalLink I4
sumBettis I5'
degrees I4
I5 = generalHomogeneousLinkage({2,2,5},I4)
sumBettis I5


kk = ZZ/32003
S' = kk{x,y,z}
describe S'
J = sub(I', S')
d1 = mingens J
d2 = syz d1
d3 = syz d2
syz d3
C = complex{d1,d2,d3}
C.dd^2
prune HH C
f = d1_0_0
Jf = ideal diff(vars S', f)
f % Jf
f0 = ((gens Jf)*(f//gens Jf))_0_0
matrix{{f}} % ideal(((gens Jf)*(f//gens Jf)))
factor f0
factor f
quotientRemainder (matrix{{f}}, ((gens Jf)*(f//gens Jf)))
quotientRemainder (((gens Jf)*(f//gens Jf)), matrix{{f}})
(-15350*2629^2)_kk
T = exteriorTorModule(gens I', S^1/I');
leadTerm ann T
BK = basicKoszulSyzygies I'
G = localResolution I'
F = res I'


    


--------------

isLicci ideal(x^3,x^2*y^2,y^4,x^2*y*z,x*y*z^2,y^2*z^2,z^3)

L = II/isLicci ;
f = ell -> not ell
T = positions(L, (ell -> ell === false))
M = II_T -- list of non-licci ideals
MM = M/cvwh1
use S
I = monomialIdeal(x^3,x^2*y^2,y^4,x^2*y*z,x*y*z^2,y^2*z^2,z^3)
hu I
I = monomialIdeal(x^3,x^2*y^2,y^3,x^2*y*z,x*y*z^2,y^2*z^2,z^4)
minimalBetti ideal I
minimalBetti monomialLink I
M/isLicci
#M
M0 = monomialIdeal(x^3,x^2*y^2,x*y^3,y^4,x^2*y*z,x*y^2*z,z^5)
I = generalLink M0;
elapsedTime I = generalLink I;
elapsedTime (J0,J) = pregeneralLink ideal(I_*);
numgens J
numgens J0
S' = localRing(S, ideal vars S)
elapsedTime quotient(J0,J,Strategy => Quotient); -- 15 sec
elapsedTime quotient(J0,J,Strategy => Iterate); -- 7 -- the winner! and the default.
T = ZZ/32003[t,x,y,z]
J0h = ideal apply(J0_*, f-> homogenize(sub(f,T),t));
Jh = ideal apply(J_*, f-> homogenize(sub(f,T),t));
elapsedTime  J0h: Jh;
mingens oo

elapsedTime gb J0;
elapsedTime gb ideal(J_*);
for f in J_* list elapsedTime J0:f;
elapsedTime intersect oo;
for i from 0 to numgens J -1 list 
elapsedTime syz (matrix{J_*}|matrix{J0_*});
elapsedTime groebnerBasis (ideal(J_*), Strategy => "F4");
elapsedTime G = groebnerBasis (ideal(J0_*), Strategy => "F4");
m = transpose gens J | (target transpose gens J)**G;
elapsedTime syz(gb (m, Syzygies => true, SyzygyRows => 1, Strategy => LongPolynomial));
T = ZZ/32003[t, x,y,z]--, MonomialOrder => Eliminate 1]
elapsedTime groebnerBasis (t*sub(J0, T)+(1-t)*ideal(sub(J_0,T)) , Strategy => "F4")

--elapsedTime quotient(sub(J0,S'),sub(J,S'),Strategy => Local); --Looooong


sumBettis J
sumBettis I
J = I

evol = I -> (
    while I != ideal (1_S) do(
    <<sumBettis I<<", ";
    (pure,mix) := hu I;
    I = pure:mix);
    <<endl<<endl;
)    
M/evol

pure = ideal "x8, y8, z8"
mix = (ideal"xyz")^5--*ideal"xy,xz,yz"    
betti res (pure+mix)
(pure, mix) = hu(pure:mix)
betti res (pure+mix)
count = -1
II/(I -> (count = count+1; << count<<endl; isLicci I;<<endl<<endl))

I = monomialIdeal(x^4,x^2*y,x*y^2,y^4,x^2*z,x*y*z,z^4)
I == monomialIdeal(x^4,x^2*y,x*y^2,y^4,x^2*z,x*y*z,z^4)
betti res I
isLicci I
I = II_33
betti res I
isLicci I
I = monomialIdeal(x^3,x*y^2,y^4,x*y*z,y^2*z,z^4)

L'/(I-> testGolod I)

--II/(I->annihilator exteriorTorModule I)
II/(I-> cvw I);
I = last II

I0 = II_4
--I' = doubleLink I0
I' = generalLink I0
cvw I0
betti (F = localResolution I')
om = dual F.dd_3
I'' = generalLink I'
R = S/I''
red = map(kk,R,{3:0})
omR = sub(om,R)
red gens ker omR



restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
M = ideal vars S
setMaxIdeal M

localNumGens = J -> prune (module J)/M*(module J)

d = 4 -- there are 6 golod monomial ideals with d=4, n=6. I only got through one, and partly a second.
n = 6
I0 = monomialIdeal apply(numgens S, i->S_i^d)
L = orbitRepresentatives(S, I0, n-3:d)
l = L/regularProducts
L' = L_(positions(l, t -> t))
L'_2
(L'/cvw)
cvw(L'_5)
I = L'_5
isGolod(S/I)
T = exteriorTorModule(gens I, res I)
E = ring T
ann prune((ideal vars E)*T)
I' = generalLink I
              0 1 2 3
oo34 = total: 1 6 8 3
           0: 1 . . .
           1: . . . .
           2: . 2 . .
           3: . 2 2 .
           4: . 2 4 .
           5: . . 2 3

betti res I'
T' = exteriorTorModule(gens I', res I');
E' = ring T'
ann prune((ideal vars E')*T')
--it's golod!
I'' = doubleLink I';
localPrune module I'' -- still 6 gens
elapsedTime I''' = doubleLink I''; -- 47 sec
elapsedTime localPrune module I''' -- slow!

elapsedTime res localTrim I'''
elapsedTime d1 = localMingens gens I'''; -- fast!
d2 = localsyz d1; -- slow!
F = res I''' -- fast
needsPackage "PruneComplex"
pruneComplex o24
elapsedTime H = minBetti I'''

rank H_1
#H
apply(#H, i-> H_i)

describe S
S' = kk{x,y,z}
kk = coefficientRing S'
J = sub(I''', S');
F' = res J
errorDepth = 0
redd' = map(kk, S', {numgens S':0})
Fbar' = redd F'
prune HH Fbar' -- fast!

K = ideal mingens J; -- fast!
K = ideal K_*;
res( K, Strategy => 2) -- nope
gens gb K;
gbTrace = 0
gens gb K;


I = L_6
basicKoszulSyzygies I
F = res I
F.dd_2
T = exteriorTorModule(gens I, res I);
ann oo
E = ring T
prune ((ideal vars E)*T)
ann oo
gens I




cvw L_3
S' = (ZZ/32003){x,y,z}
J' = sub(localTrim J, S');
F = res J'
F.dd_3_0_0
betti oo
L = select(orbitRepresentatives(S, I0, n-3:d)/ideal, I -> testGolod I)
L/minimalBetti
for I' in L do(
    <<sumBettis I'<<endl;
    apply(2,i-> (
	I' = doubleLink I';
	<<sumBettis I'<<flush<<endl;
	));
<<endl;
)

I = L_0
I = ideal(x^3,x^2*y,x*y^2,y^3,x^2*z,x*y*z,y^2*z,z^3)
assert(isGolod(S/I) == true)
betti res I
assert(sumBettis I == 26)
I' = generalLink I
isHomogeneous I'
betti res I'
assert(isGolod(S/I') == true)
sumBettis I' == 26
I'' = generalLink I';
isHomogeneous I'' == false

R = S/I''
K = koszul vars R
apply(4, i-> numgens prune HH_i K)
tI'' = localTrim I''
localResolution tI'' 
basicKoszulSyzygies I''

restart
load "Linkage.m2"
J = CLKW 32003
S = ring J
cvw J

minimalBetti J
S= ZZ/32003[x,y,z]
M = ideal vars S
I = (ideal vars S)^3
J = doubleLink I
trim J
J' = doubleLink J;
elapsedTime J''= doubleLink J'

elapsedTime F = res J'
kk = coefficientRing S
redd = map(kk, S, {numgens S:0})
Fbar = redd F
prune HH Fbar -- fast!

restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
I = ideal"xyz, x3+xz2, y3+yz2, z3, x4+y4-x2y2"
betti res I
cvwh I


-------monomial Linkage after Huneke-Ulrich
restart
load "Linkage.m2"
S = ZZ/101[x,y,z]
d = 4
use S
I0 = monomialIdeal apply(gens S, x -> x^d)
L = orbitRepresentatives(S, I0, toList(4,4,4,4,5))
L/isLicci

--example of non decreasing sumBettis
I = ideal(x^4,x^3*y,y^4,x^2*z^2,y*z^3,z^4)
sumBettis I
I' = I
minimalBetti I'
I' = monomialLink I'
cvwh1 I
I' = bestHomogLink I'_0
minimalBetti I'_0
isGolod(S/I'_0)
J = generalLink I'_0

--alternates!
sumBettis J
--isLicci I
testGolod I' -- false
isGolod(S/I') -- false
cvw I' -- general Link does decrease; this is ultimately Golod.
 

I = monomialIdeal(x^3,x^2*y,y^3,x^2*z,x*y*z,z^3)
testGolod I
betti res I
isLicci I
cvw I
I = monomialLink I
betti res oo
test
testGolod(monomialLink I)
--so the non-Licci ideal I becomes Golod after one more 
--monomial link.

use S
I =ideal(x^4,x^2*y^2,y^4,x^2*y*z,x*y*z^2,y^2*z^3,z^4)
testGolod I
I= monomialLink I
testGolod I
I= monomialLink I
testGolod I --false
minBetti I
elapsedTime I = generalLink I; isGolod(S/I) -- true
minBetti I
--the monomial linkage came within 1 general links of golod

monomialIdeal(x^4,x^2*y^2,y^4,x*y*z^2,x^2*z^3,z^4)
testGolod I;sumBettis I
I= monomialLink I
testGolod I;sumBettis I
I= monomialLink I
testGolod I;sumBettis I
minBetti I 
elapsedTime I = generalLink I; isGolod(S/I)
minBetti I
elapsedTime I = generalLink I; isGolod(S/I) -- true
minBetti I
--the monomial linkage came within 2 general links of golod
elapsedTime I = generalLink I; isGolod(S/I) -- true
minBetti I

use S
I = monomialIdeal(x^4,x^3*y,y^4,x^2*z^2,y^2*z^3,z^4)
testGolod I, sumBettis I

I= monomialLink I
testGolod I,sumBettis I
I= monomialLink I
testGolod I,sumBettis I
minBetti I 
elapsedTime I = generalLink I; isGolod(S/I)
minBetti I
elapsedTime I = generalLink I; isGolod(S/I) -- true
minBetti I
--the monomial linkage came within 2 general links of golod
elapsedTime I = generalLink I; isGolod(S/I) -- true
minBetti I

restart
load "Linkage.m2"
S = ZZ/101[x,y,z]
I= monomialIdeal(x^4,x^3*y,x^2*y^3,y^4,x^2*y*z,x*y*z^2,y^2*z^2,z^4)
hu I
cvwh1 I
isGolod(S/ideal(y^2+17*x*z+y*z+32*z^2,x*y-9*x*z-39*y*z+43*z^2,x^2-14*x*z+30*y*z+32*z^2,z^3,y*z^2,x*z^2))
 testGolod I,sumBettis I
I= monomialLink I
testGolod I,sumBettis I
I= monomialLink I
testGolod I,sumBettis I
I= monomialLink I
testGolod I,sumBettis I
I= monomialLink I
testGolod I,sumBettis I
minBetti I 
elapsedTime I = generalLink I; isGolod(S/I)
minBetti I
elapsedTime I = generalLink I; isGolod(S/I) -- true
minBetti I
--the monomial linkage came within 2 general links of golod
elapsedTime I = generalLink I; isGolod(S/I) -- true
minBetti I

--
restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
J1 = ideal(x)
I1 = ideal apply(3,i-> rand(5,J1))

J2 = ideal (y,z)
I2 = ideal apply(3, i-> rand(4+i, J2))
I = I1+I2
I = ideal random(S^1, S^(-{3,4,5,6,6}))
minimalBetti I
cvwh1 I
sum
I = bestHomogLink I
I =  bestHomogLink I_0
minimalBetti I_
isGolod(S/I_0)

use S
I = ideal(x^4,x^3*y,x^2*y^2,y^4,x^3*z,x*y^2*z,z^4)
minimalBetti I

I = (ideal"x3,y3,z3":I)
minimalBetti I
cvwh1 I
I = bestHomogLink I
I =  bestHomogLink I_0

orbitRepresentatives(S, {2,2}, MonomialType => "SquareFree")

restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]

use S
I = ideal"x5,y5,z5,xy,xz"
I' = (bestHomogLink I)_0
I'' = (bestHomogLink I')_0
--complete intersection type 1,1,4
J = generalLink generalLink I
netList J_*
trim ideal"12575x - 8560y, 5123x + 14499z,- 13788y - 11732z"
--so the "leading" linear forms in the generators of J generate (x,y,z).

generalHomogeneousLinkage({2,5,5},I)
betti res oo
I'= (bestHomogLink ())_0--isLicci I
cvwh1 I
--I = ideal"x3,y5,z5" :I


sumBettis generalLink I
generalHomogeneousLinkage({2,5,5},I)
generalHomogeneousLinkage({2,2,5},I)
betti res oo

-----
--attempt non-licci primary monomial ideals with high regularity.
restart
load "Linkage.m2"
--possible conjectures: 
--1) min last twist > (g-1)*max gen degree => licci
--2) FALSE for 3,4 vars: if codim I_mixed >= 2 then max last shift <= (g-1) min gen degree.
--3) FALSE: in codim 3, codim I_mix >= 2 implies golod.
n = 3
S = ZZ/101[x_0..x_(n-1)]
d = 7
I0 = monomialIdeal apply(gens S, a -> a^d)
II = orbitRepresentatives(S,I0,toList(3:d));
lastbettis = I-> (select(keys minimalBetti I, k-> k_0==n))/last
elapsedTime B = for I1 in II list lastbettis ideal(I0+I1);

Q = positions(II, I-> codim I >= 2)
B2 = B_Q
positions(Q, q-> max (B_q) > (n-1)*d)
minimalBetti ideal(I0+II_63)

P = positions(B/min, i-> i>(n-1)*d)
for p in P list codim((hu(I0+II_p))_1)
netList for p in P list minimalBetti monomialLink monomialLink (I0+II_p)
for p in P list isLicci (I0+II_p)

I = I0+II_63
I' = generalLink I
minimalBetti I'
I'' = generalLink I'

betti res I'
minimalBetti I''




s = product(n, i->S_i^((d-1)//(n-1)))
I1 = ideal apply(n, i-> ideal(s):ideal(S_i^((d-1)//(n-1))))
I1 = ideal(product(3,i->S_i), product(3,i->S_(i+3)))
I = I0+I1



What property of the mixed part implies Golod?

restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
M = ideal vars S
setMaxIdeal M
I0 = monomialIdeal"x4,y4,z4"
II = orbitRepresentatives(S,I0,{4,4,4,4,3,3});
#II
cvwh1 II_0

elapsedTime for i from 0 to #II-1 do <<i<<" "<<isLicci II_i<<endl;
testGolod ideal(x^3,x^2*y^2,y^4,x^2*y*z,x*y*z^2,y^2*z^2,z^3);
elapsedTime allGolod = apply(II, I-> {testGolod I, testGolod (hu I)_1, I})
all(select(allGolod, p -> p_0 == true), p-> p_1) -- whenever J Golod, mix J is Golod 
   --because a nonzero mult on mix J would persist after making the pure powers large.

all(select(allGolod, p -> p_0 == true),p -> pdim module p_2 == 1) 
   -- but there are Golod J with non perfect mix J

findMonomialGolod = II -> apply(#II, i ->(
--	<<i<<endl;
     I:= II_i;
    (p,m) := (hu I);     
    J := p:m;
     while (p != J and J != I) do (
        I = J;
        (p,m) = hu I;
        J = p:m;
        (p,m) = hu J;
        J = p:m);
    if not testGolod J and testGolod m then J else 0
    ))

mix = J -> (hu J)_1 -- find the mixed part.

S = kk[x,y,z]
I0 = monomialIdeal"x4,y4,z4"

II = orbitRepresentativesLis(S,I0,{4,4,4});
allmons = subsets((ideal vars S)^4_*, 3)/(L -> trim(ideal L))
#allmons == binomial(15,3)
II = select(apply(allmons, I -> trim(I + ideal"x4,y4,z4")), I -> numgens I == 6);
#II
perf = select(II, I -> (J = mix I; codim J == 2 and pdim module mix I == 1));
#perf
golodPerf = select(perf, I -> testGolod I)
nonGolodPerf = select(perf, I -> not testGolod I)
I =  nonGolodPerf_0
mix I
betti res mix I
codim mix I
testGolod mix I
netList apply(nonGolodPerf, I -> minimalBetti mix I)
last nonGolodPerf
mix oo

--Prop J golod => mix J golod. Proof: otherwise there would be nontrivial mult when we take 
--high degree pure part.
 
--if J is not golod then the mixed part may be golod
--and in this case the saturation of the mixed part seems to be golod too.
--also if J is not golod and the mixed part is golod then the mixed part may be perfect or not

--Question: if the mixed part is perfect of height 2 (so Golod) is J golod? NO;
-- eg monomialIdeal(x^4,x^3*y,x*y^2,y^4,x^3*z,y^2*z,z^4)
--Note: can't tell from the degree matrix of the resolution of the perfect codim 2 case whether
--the whole ideal is Golod or not. Also, when the degree matrix of the perf codim 2 ideal
--has no "ghost" terms, then the total ideal may not be Golod: for example,
--(x^4,x^3*y,y^4,x^2*z^2,y*z^3,z^4).

--But: is possible that if K is perfect codim 2 with linear res (maybe not even monomial)
--then (K + pure powers) is Golod?






elapsedTime L = findMonomialGolod II

elapsedTime perf = select(II, I -> (
	m:= (hu I)_1;
	codim m == 2 and pdim module m == 1));
#perf
perf/testGolod
perf/(J -> degrees syz gens J)
perfgolod = select(perf,(J -> testGolod J));
#oo
perfnotgolod = select(perf,(J -> testGolod J === false));
#oo

mixGolod = perfgolod/(I -> (hu I)_1);
all(mixGolod, I -> testGolod I) -- mix J perfect, J Golod => mix J golod.

mixNotGolod = perfnotgolod/(I -> (hu I)_1);
degsGolod = apply( mixGolod, I -> degrees syz gens I);
degsNotGolod = apply( mixNotGolod, I -> degrees syz gens I);
#degsGolod
netList unique degsGolod
netList unique degsNotGolod


#unique (unique degsGolod|unique degsNotGolod)


testing "no ghost perfect mix J implies J golod"
kk = ZZ/101
S = kk[x,y,z, Degrees => {{1,0,0},{0,1,0},{0,0,1}}]

num = 3
D = {{1,2,3},{3,3,2},{2,3,4},{2,2,2}}
E = {{5,4,4},{4,5,6},{6,5,4}}
map(S^(-D), S^(-E), (i,j) -> (L = E_j-D_i;
	                      product(3, k -> S_k^(if L_k>0 then L_k else 0))))

	     


betti res (hu perfgolod_1)_1
betti res (hu perfnotgolod_1)_1


testGolod (hu perf_0)_1
betti res betti res (hu perf_0)_1
testGolod perf_0

L = select(L, ell -> ell =!=0)
L/(ell -> pdim module ell)
L/(ell -> testGolod(saturate ell))
I = L_0
testGolod I
(p,m) = hu I
testGolod m
all(L/(ell -> ell_1), t -> t)


M = L/(ell -> (hu ell)_1)
M/degree

degs = {4,4,4}
S = ring L_0 
I0 = monomialIdeal apply (3, i-> S_i^(degs_i))
L' = M/(m-> monomialIdeal I0+m)
L'/testGolod

netList (M/(m -> betti res m))
M' = M/(m -> testGolod(I0+saturate m))
testGolod( I0+saturate M_9)
m = M_9
saturate m
primaryDecomposition m

M/testGolod
L'' = M/(m -
testGolod ideal(y*z,x*y,x^2*z,y^3,x^3,z^4)        

testGolod I'
	

(p,m) = hu ideal(x^3,x^2*y^2,y^4,x^2*y*z,x*y*z^2,y^2*z^2,z^3)

I' = p:m
(p,m) = (hu I')
testGolod I'

--Looking for monomial ideals of codim 2 with linear res
needsPackage "MonomialOrbits"
load "Linkage.m2"
S = ZZ/101[x,y,z]
d = 4
mm = ideal vars S
ze = monomialIdeal 0_S
elapsedTime II = orbitRepresentatives(S,ze,mm^d,5)
I = II_0
select(II, 
    I -> (
	F = res module I;
	max flatten degrees F_(length F) == d+length F
	)
    )

IIT = apply(II, 
    I -> (
	F = res module I;
	max flatten degrees F_(length F) == d+length F
	)
    );
IILin = II_(positions (IIT, s -> s));
IILinPerf = partition(I-> pdim module I == 1, IILin)
#IILinPerf#true
#IILinPerf#false
JJ = select(IILinPerf#true, I -> 
    contract(gens I1,gens I) == 0
    )
for I in JJ list testGolod(I+I0)
I = JJ_0
betti res I
J = I+ I0
testGolod(J' = I0:J)
(Jp,Jm) = hu J'
betti res Jm
I1 = monomialIdeal(x^4,y^4,z^4)
betti res J
J' = minHomogLink J
betti res J'
J'' =   minHomogLink J'
betti res J''
J''' =   minHomogLink J''
betti res J'''
J'''' =   minHomogLink J'''
betti res J''''
isGolod(S/J'''')
betti res J'
I0= monomialIdeal(x^5,y^5,z^5)

betti res IILin_73

betti res (I = II_27)
oo I
flatten degrees F_(length F) 
== d+length F

---
restart
load"Linkage.m2"
--viewHelp MonomialOrbits
kk = ZZ/32003
S = kk[a,b,c,d]
mm = ideal vars S
d = 4
I0 = monomialIdeal (a^d)
I1 = ideal apply(gens S, x -> x^d)
J = trim ideal (gens (mm^d) %I1)

elapsedTime II = orbitRepresentatives(S,I0,J,6);#II
elapsedTime II3=select(II, K -> codim K == 3);#II3
elapsedTime IICM=select(II3, K -> length res K == 3);#IICM
elapsedTime select(IICM, I -> falsetrue I)
elapsedTime T=select(IICM, I -> truetrue I);#T
elapsedTime GCI =select(T, I-> isGenericallyCI I)
elapsedTime T=select(GCI, I -> truetrue I)
--for 6 mons of degree 4, all the genci strongly nonobs link in 1 step to aci

for I in  T list betti res I
I = T_0 --links to aci
A = ideal"a4,b2c2,c2d2+bd3";codim A
I' = A:I
I = T_1 --links to aci
A = ideal"a4,b2c2,c2d2+bd3";codim A
I' = A:I
I = T_2 --links to aci
A = ideal"a4,bc3,c3d+bd3";codim A
I' = A:I


--trying for linkage equivalence in 3 variables, m-primary, monomial
restart
load"Linkage.m2"

prepMomonialPair = (P1,P2) ->(
I3 := isLicciMonomialIdeal P1;
I8 :=  isLicciMonomialIdeal P2;
--I3' := weakPolarization(I3, "AllVars" => true);
--I8' := sub(weakPolarization(I8, "AllVars" => true), ring I3');
I3' := polarize I3;
I8' := polarize I8;
R := coefficientRing ring I3[z_{0,0}..z_{2,3}];
I3' = sub (I3', R);
I8' = sub (I8', R);
(I3', I8'))



indistinctPairs = (T,LL) -> (
    for L in LL list(
	test(T_(L_0),T_(L_1))))
viewHelp MonomialOrbits
restart
load"Linkage.m2"
kk = ZZ/32003
S = kk[a,b,c]
mm = ideal vars S
d = 4
I0 = monomialIdeal"a3,b4,c5"
II = orbitRepresentatives (S,I0,{3,3,4,4,5,5});#II
II = II/reducedForm;
T = select (II,I-> I != 1);#T

T = flatten for i from 0 to #T-2 list
        for j from i+1 to #T-1 list
        if II_i != II_j then (II_i, II_j) else
	continue;#T

elapsedTime linkedT = flatten for i from 0 to #T -2 list
        for j from i+1 to #T-1 list(
	Ij' := monomialLink1 II_j;
        if II_i != Ij' then (II_i, Ij') else
	continue);#linkedT

--HTest345 = apply(T, t -> koszulHomologyTest t);
linkedHTest345 = apply(linkedT, t -> koszulHomologyTest t);
	                
netList Htest345
elapsedTime test345 =  apply(T, t -> test t);
select(Htest345, u -> all u)


class test345    
--indistinguishables = {{3, 8}, {5, 10}, {11, 45}, {13, 49}, {16, 26}, {16, 111}, {17, 27}, {17, 29}, {20,
       ------------------------------------------------------------------------------------
       30}, {23, 47}, {26, 111}, {27, 29}, {43, 60}, {43, 125}, {50, 120}, {59, 141}, {60,
       ------------------------------------------------------------------------------------
       125}, {65, 80}, {68, 76}, {73, 109}, {74, 86}, {84, 88}, {87, 101}, {92, 131}, {96,
       ------------------------------------------------------------------------------------
       102}}

test(T_3,T_8)

test (T_0,T_1)
elapsedTime IT = indistinctPairs TNotEqual_{0..1000};
L = TNotEqual_{0..1000};
possiblyLinked = select(L, ell->all test(T_(ell_0), T_ell_1))
possiblyLinked == {{0, 4}}

I1 =T_0
I2 =T_4
degree (S^1/I1)
degree (S^1/I2)
I = intersect(I1, I2)
rs2 = ideal(random(3,I), random(4,I))
isIsomorphic (module(I1/rs2), module(I2/rs2))
betti res I1
betti res I2
rs = ideal(random(3,I1), random(4,I1), random(5,I1));codim rs
rs = ideal"a3,b4,c5";
I1' = rs:I1
degree (S^1/I1')
degree (S^1/I2)
for i from 1 to 4 list degree HH_i (koszul gens I1)
for i from 1 to 4 list degree HH_i (koszul gens I1')
for i from 1 to 4 list degree HH_i (koszul gens I2)
360-10*34
279-10*26
TNotEqual_10
test(T_0,T_11)
P1 = T_0;P2=T_11
 netList IT
TNotEqual_0
elapsedTime Q = test(3,8)
elapsedTime netList for L in indistinguishables list test(L_0,L_1)
isLicciMonomialIdeal II_13
isLicciMonomialIdeal II_49
{{0, 15}, {2, 17}, {3, 18}, {6, 20}, {7, 21}}
TNotEqual =flatten for i from 0 to #T-2 list
                   for j from i+1 to #T-1 list
		   if T_i!=T_j then {i,j} else continue;
TNotEqual		   

indistinctPairs = LL -> (
          for L in LL list(
      	test(II_(L_0),II_(L_1))))

o68 = indistinctPairs

o68 : FunctionClosure

i69 : elapsedTime IT = indistinctPairs TNotEqual;
 -- 82

Indist pairs after eliminating licci's and pairs actually equal
ITAllIndices for powers 3,4,5 and 7 more quartics
ITAllIndices = {50274, 50363, 50538, 50624, 52186, 53652, 53686, 53781, 53866, 54163, 54218, 54220, 54221, 54225, 54226, 54233}


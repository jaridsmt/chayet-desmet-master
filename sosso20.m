/* =====================================================================
   Verification that

       2n * eps( a^2 b^2 - (ab)^2 )   =   the given sum of five families
                                          of squares

   in the algebra A with basis {e_X}, X running over the singletons, the
   2-subsets and the 4-subsets of {1..n}.
   Optimised rewrite of so20_script.magma.

   Two modes:
       SYMBOLIC_N := true    n is a formal variable: the identity is
                             verified in Q(n), hence for ALL n at once.
       SYMBOLIC_N := false   the identity is verified for the integer n
                             set below.
   


   ---------------------------------------------------------------------
   WHAT THIS SCRIPT DOES
   ---------------------------------------------------------------------
   (1) POLARISATION.  The identity is bihomogeneous of degree (2,2) in
       (a,b). Hence the identity can be checked by setting

            a = s*e_I + t*e_J ,      b = u*e_K + v*e_L ,

       i.e. by working in a polynomial ring with FOUR variables.  Each
       polynomial on the SOS side is an alternating form  L = sum_{P,Q} C[P][Q] x_P y_Q, so
       after the substitution only the four entries C[I][K], C[I][L],
       C[J][K], C[J][L] survive. 

   (2) SYMMETRY.  The expression is invariant under the action of $S_n.
       With the a <-> b symmetry this leaves 3065 orbits of monomials to check.
=================================================================================*/

SYMBOLIC_N := true;  // true : verify in Q(n), i.e. for all n at once
                     // false: verify for the integer n below
n := 20;             // used only when SYMBOLIC_N is false

VERBOSE   := false;  // true: print one line per orbit

/* ---------------------------------------------------------------------
   0.  Coefficient field, working universe.

   Every configuration (I,J,K,L) has support inside {1..16}, so a universe
   of 17 elements is enough in the symbolic case: one element outside the support is needed
   as a standin for the type 5 polynomials h_{A,k} 
   --------------------------------------------------------------------- */
Fsym<N> := RationalFunctionField(Rationals());   // N prints as "N"
if SYMBOLIC_N then
    F := Fsym;
    nsym := N;
    univ := {1..17};
else
    //n ge 7 is simply to ensure everything is well-defined.
    assert n ge 7;
    F := Rationals();
    nsym := F!n;
    univ := {1..n};
end if;
R<s,t,u,v> := PolynomialRing(F, 4);
t_start := Cputime();

/* ---------------------------------------------------------------------
   1.  The sign function denoted \sigma(A,B) in the paper.
   It is only ever called with (#A,#B) in {(2,4),(4,2),(4,4)}.
   --------------------------------------------------------------------- */
function det_sign_man(twoset, fourset)
    if #fourset eq 2 and #twoset eq 4 then
        return det_sign_man(fourset, twoset);
    end if;
    twoset_ind := Sort(Setseq(twoset));
    common := twoset meet fourset;
    if #twoset eq 2 then
        if #common eq 1 then
            result := 1;
            for elt in fourset do
                if elt lt twoset_ind[2] and elt gt twoset_ind[1] then
                    result := -result;
                end if;
            end for;
            return result;
        else
            return 0;
        end if;
    else
        if #common eq 3 then
            exponent := 0;
            for elt in common do
                for elt2 in (twoset sdiff fourset) do
                    if (elt2 notin common) and elt2 lt elt then
                        exponent := exponent + 1;
                    end if;
                end for;
            end for;
            return (-1)^exponent;
        elif #common eq 2 then
            exponent := 1;
            for elt in common do
                for elt2 in (twoset sdiff fourset) do
                    if (elt2 notin common) and elt2 lt elt then
                        exponent := exponent + 1;
                    end if;
                end for;
            end for;
            for elt in (twoset diff common) do
                for elt2 in (fourset diff common) do
                    if elt gt elt2 then exponent := exponent + 1; end if;
                end for;
            end for;
            return (-1)^exponent;
        else
            return 0;
        end if;
    end if;
end function;

/* ---------------------------------------------------------------------
   2. Function implementing the multiplication of two basis elements (represented by subsets). 
       Elements of the algebra are stored as an associative array with keys
       subsets (corresponding to basis elements) and value the coefficient corresponding to that basis element.
   --------------------------------------------------------------------- */
function bmul(X, Y)
    if #X gt #Y then
        return bmul(Y, X);
    end if;
    if X eq Y then
        return [<{i}, F!1> : i in X];        // e_X^2 = sum_{i in X} e_i
    end if;
    lx := #X; ly := #Y;
    if lx eq 1 then
        //if ly is 1, then we return 0 at line 215, because X==Y was already handled in l.203
        if Rep(X) in Y then
            if ly eq 2 then
                return [<Y,F ! 1/2>];
            end if;
            return [<Y, 1/4>];
        end if;
        return [];
    end if;
    sd := X sdiff Y;
    if ly eq 2 then                          // 2 subset x  2 subset
        if #sd eq 2 then 
            return [<sd, F!(1/2)>]; 
        end if;
    elif lx eq 2 then                        // 2 subset x 4 subset
        if #sd eq 4 then
            return [<sd, F!(1/4) * det_sign_man(X, Y)>];
        end if;
    else                                     // 4 subset x 4 subset
        if #sd eq 2 or #sd eq 4 then
            return [<sd, F!(1/2) * det_sign_man(X, Y)>];
        end if;
    end if;
    return []; //return 0 when none of the cases above occur.
end function;

//This function takes two arbitrary elements of A (stored as associative arrays) and multiplies them.
function emul(E1, E2)
    out := AssociativeArray();
    for X in Keys(E1) do
        for Y in Keys(E2) do
            pr := E1[X] * E2[Y];
            if pr ne 0 then
                //this for loop adds the contribution of E1[X]X * E2[Y]Y to out
                 for tp in bmul(X, Y) do
                    Z := tp[1]; c := tp[2] * pr;
                    if IsDefined(out, Z) then
                        out[Z] := out[Z] + c;
                    else
                        out[Z] := c;
                    end if;
                end for;
            end if;
        end for;
    end for;
    return out;
end function;

function counit(E)
    r := R!0;
    for Z in Keys(E) do
        if #Z eq 1 then r := r + E[Z]; end if;
    end for;
    return (1/nsym) * r;
end function;

// 2n*eps(a^2 b^2 - (ab)^2) for a = s e_P1 + t e_P2, b = u e_Q1 + v e_Q2.
// (The 2n ensures this side does not depend on n, for given P1,P2,Q1,Q2.)
function norton_side(P1, P2, Q1, Q2)
    a := AssociativeArray();
    b := AssociativeArray();
    a[P1] := s;
    if IsDefined(a, P2) then a[P2] := a[P2] + t; else a[P2] := t; end if;
    b[Q1] := u;
    if IsDefined(b, Q2) then b[Q2] := b[Q2] + v; else b[Q2] := v; end if;
    a2 := emul(a, a); b2 := emul(b, b); ab := emul(a, b);
    return 2 * nsym * (counit(emul(a2, b2)) - counit(emul(ab, ab)));
end function;

/* ---------------------------------------------------------------------
   4.  The squares.  A square is encoded as a tuple <k, T, i>:

       f_T:     <1, T, 0>   type 1,  T a 2-set                weight 1
       f_F,i:   <2, F, i>   type 2,  F a 4-set, i in F        weight 1/8
       f_S:     <3, S, 0>   type 3,  S a 6-set                weight 2
       g_T:     <4, T, 0>   type 4,  T a 2-set                weight (20-n)/(n-2)
       h_{T,i}: <5, T, i>   type 5,  T a 2-set, i notin T     weight 2
   --------------------------------------------------------------------- */
   

function sqweight(k)
    case k:
        when 1: return F!1;
        when 2: return F!1/8;
        when 3: return F!2;
        when 4: return (20 - nsym )/(nsym - 2);  ;
        when 5: return F!2;
        else    return F!0;
    end case;
end function;


//this is the sign appearing in type 3 polynomials
function delta6(A1,A2);
    common := Setseq(A1 meet A2)[1];
    A1seq := Setseq(A1);
    A2seq := Setseq(A2);
    exponent := Index(A1seq,common) - Index(A2seq, common);
    G := Sym(A1 sdiff A2);
    perm := G! (Setseq(Exclude(A1,common)) cat Setseq(Exclude(A2,common)));
    return (-1)^exponent*Sign(perm);
end function;

//this is the sign appearing in type 5 polynomials 
function delta24(i,k,A);
    G:= Sym({i,k} join A);
    return Sign(G ! ([i] cat [k] cat Setseq(A)));
end function;

/* Function that returns the coefficient C[X][Y] at X Y of the polynomials in the SOS-side.  
Note that each polynomial is alternating: C[Y][X] = -C[X][Y]. 
sq is of the form <k,T,i>, where k denotes the type of polynomial, and T and i are 
the set T and element i that determine the polynomial.
i is set to zero when no element is necessary.
*/
function sqcoeff(sq, X, Y)
    if X eq Y then 
        return F!0; 
    end if;
    if #X gt #Y then 
        return -sqcoeff(sq, Y, X); 
    end if;
    k := sq[1]; T := sq[2]; i := sq[3];
    lx := #X; ly := #Y;
    ip := X meet Y;
    case k:
      when 1: //Polynomial f_T, #T=2
        if lx eq 1 and ly eq 2 then
            if Y eq T and X subset Y then
                return (Minimum(T) in X) select F!1 else F!(-1);
            end if;
        elif lx eq 2 and ly eq 2 then
            if (X sdiff Y) eq T then
                return (Minimum(T) in X) select F!1 else F!(-1);
            end if;
        end if;
        return F!0;
      when 2: //Polynomial f_{T,i} #T=4 , i\in T
        if lx eq 1 and ly eq 4 then
            if Y eq T and X subset T then
                return (i in X) select F!(3) else F!(-1);
            end if;
        elif lx eq 2 and ly eq 4 then
            if (X sdiff Y) eq T then
                c := (i in X) select F!(3) else F!(-1);
                return c * det_sign_man(X, T);
            end if;
        elif lx eq 4 and ly eq 4 then
            if (X sdiff Y) eq T then
                c1 := ((i in X) select F!(2) else F!(-2))
                          * det_sign_man(X, T);
                return c1;
            end if;
        end if;
        return F!0;
      when 3: //Polynomial f_T, #T=6
        if lx eq 4 and ly eq 4 and (X sdiff Y) eq T then
            //take a canonical pair to set signs.
            return F!(delta6(X,Y));
        end if;
        return F!0;
      when 4: //Polynomial g_T #T=2
        if lx eq 4 and ly eq 4 and (X sdiff Y) eq T then
            if Minimum(T) in X then
                return F!(det_sign_man(T, X));
            else
                return F!(-det_sign_man(T, Y));
            end if;
        end if;
        return F!0;
      when 5: //Polynomial h_{T,i}, #T=2, i\notin T
        if lx eq 4 and ly eq 4 and (X sdiff Y) eq T then
            A := (Minimum(T) in X) select X else Y;
            cc := (i in ip) select -(nsym - 5)/(nsym - 2)
                            else F!3/(nsym - 2);
            c := cc * det_sign_man(T, A);
            return (Minimum(T) in X) select c else -c;
        elif lx eq 2 and ly eq 4 then
            if X subset Y and (Y diff X) eq T and i in X then
                other := Rep(X diff {i});
                return F!(delta24(i,other,T));
            end if;
        end if;
        return F!0;
      else
        return F!0;
    end case;
end function;



/* Given X,Y, returns a list of every polynomial whose C[X][Y] can be nonzero, each with a MULTIPLICITY.
   a pair (X,Y) can occur in a
   square in only eight relative positions (depending on #X,#Y and #X\cap Y).  Seven of them are met by at
   most four squares.  The eighth -- X, Y 4-sets meeting in 3 points --
   is met by one type-4 square and by n-2 type-5 squares (T,i), and that
   is the only place where the coefficient is not determined locally: the elements i inside the support
   S0 are listed individually, and the remaining n - #S0 values of i all
   give the same form, so they are returned once with multiplicity
   n - #S0.  (spare is an element outside S0, the local support of a monomial)  */
function squares_at(X, Y, S0, spare)
    out := [];
    if X eq Y then 
        return out; 
    end if;
    A := X; B := Y;
    //ensure that size of A is smaller than or equal to B
    if #A gt #B then 
        A := Y; B := X; 
    end if;
    la := #A; lb := #B;
    ip := A meet B;
    if la eq 1 and lb eq 2 then
        if A subset B then
            sq := <1, B, 0>; 
            Append(~out, <sq, F!1>);
        end if;
    elif la eq 1 and lb eq 4 then
        if A subset B then
            for i in B do
                sq := <2, B, i>; 
                Append(~out, <sq, F!1>);
            end for;
        end if;
    elif la eq 2 and lb eq 2 then
        if #ip eq 1 then
            sq := <1, A sdiff B, 0>; 
            Append(~out, <sq, F!1>);
        end if;
    elif la eq 2 and lb eq 4 then
        if #ip eq 1 then
            FF := A sdiff B;
            for i in FF do
                sq := <2, FF, i>; 
                Append(~out, <sq, F!1>);
            end for;
        elif A subset B then
            TT := B diff A;
            for i in A do
                sq := <5, TT, i>; 
                Append(~out, <sq, F!1>);
            end for;
        end if;
    elif la eq 4 and lb eq 4 then
        if #ip eq 3 then
            TT := A sdiff B;
            sq := <4, TT, 0>; 
            Append(~out, <sq, F!1>);
            for i in S0 diff TT do
                sq := <5, TT, i>; 
                Append(~out, <sq, F!1>);
            end for;
            if spare gt 0 then
                sq := <5, TT, spare>;
                Append(~out, <sq, nsym - #S0>);
            end if;
        elif #ip eq 2 then
            FF := A sdiff B;
            for i in FF do
                sq := <2, FF, i>; 
                Append(~out, <sq, F!1>);
            end for;
        elif #ip eq 1 then
            sq := <3, A sdiff B, 0>; Append(~out, <sq, F!1>);
        end if;
    end if;
    return out;
end function;

/* sum over all squares on the SOS side that contribute when
   a = s e_P1 + t e_P2,  b = u e_Q1 + v e_Q2.                          */
function squares_side(P1, P2, Q1, Q2)
    S0 := P1 join P2 join Q1 join Q2;
    rest := univ diff S0;
    spare := (#rest gt 0) select Minimum(rest) else 0;
    PP := [P1, P1, P2, P2];
    QQ := [Q1, Q2, Q1, Q2];
    MM := [s*u, s*v, t*u, t*v];
    cmul := AssociativeArray();
    for idx in [1..4] do
    //This for loop collects the squares of polynomials that contribute, and records their multiplicities
        for tp in squares_at(PP[idx], QQ[idx], S0, spare) do
            //Note that tp might be reached by more than one combination, 
            //but it still only occurs once in the SOS side, hence
            //we do not add coefficients together.
            cmul[tp[1]] := tp[2];
        end for;
    end for;
    total := R!0;
    for sq in Keys(cmul) do
        Lf := R!0;
        for idx in [1..4] do
            c := sqcoeff(sq, PP[idx], QQ[idx]);
            if c ne 0 then Lf := Lf + c * MM[idx]; end if;
        end for;
        if Lf ne 0 then
            total := total + cmul[sq] * sqweight(sq[1]) * Lf^2;
        end if;
    end for;
    return total;
end function;

/* ---------------------------------------------------------------------
   5.  Orbit representatives of the monomials x_I x_J y_K y_L.

   The S_n-orbit of a configuration (I,J,K,L) is determined by its 15
   "Venn multiplicities": how many ground elements lie in exactly the
   labels indexed by each nonempty subset of {1,2,3,4}.  The four row sums
   are #I,#J,#K,#L and must lie in {1,2,4}.  On top of that the expression
   is invariant under I<->J, K<->L and (I,J)<->(K,L), i.e. under the eight
   permutations of {1,2,3,4} preserving the partition {{1,2},{3,4}}.
   --------------------------------------------------------------------- */
//regions are the Venn multiplicities: 
//i.e.: 1 is I\setminus (J \cup K \cup L), {1,2} is I cap J \setminus ( K \cup L)  and so on.
regions := [Z : Z in Subsets({1,2,3,4}) | #Z ge 1];
nreg := #regions;
regpos := AssociativeArray();
for k in [1..nreg] do 
    regpos[regions[k]] := k; 
end for;

//permutations of I J K L under which the coefficient has to be invariant
perms := [[1,2,3,4], [2,1,3,4], [1,2,4,3], [2,1,4,3],
          [3,4,1,2], [3,4,2,1], [4,3,1,2], [4,3,2,1]];

//permutations of the regions which are equivalent
permreg := [[regpos[{p[z] : z in regions[k]}] : k in [1..nreg]] : p in perms];

// a vector v of venn multiplicities is only valid
// when #I = v[1] + v[{1,2}] + v[{1,2,3}] + v[{1,2,3,4}] and so on are <= 4
//states are labeled by multiplicity vectors, and the cardinalities of the sets I J K L
states := [<[Integers() | ], [0,0,0,0]>];
for k in [1..nreg] do
    Rg := regions[k];
    nxt := [];
    for st in states do
        m := 0;
        d := st[2];
        ok := true;
        while ok do
            Append(~nxt, <st[1] cat [m], d>);
            m := m + 1;
            d := st[2];
            for tt in Rg do
                d[tt] := d[tt] + m;
                if d[tt] gt 4 then 
                    ok := false; 
                end if;
            end for;
        end while;
    end for;
    states := nxt;
end for;
// We only keep those for whom I J K and L have size 1,2 or 4
types := [st[1] : st in states |
          st[2][1] in {1,2,4} and st[2][2] in {1,2,4} and
          st[2][3] in {1,2,4} and st[2][4] in {1,2,4}];


//This function reduces a vector of venn multiplicities to a "canonical" one under
//the permutations recorded in permreg
function canonkey(m)
    best := -1;
    for pidx in [1..#permreg] do
        sg := permreg[pidx];
        img := [0 : k in [1..nreg]];
        for k in [1..nreg] do 
            img[sg[k]] := m[k]; 
        end for;
        e := 0;
        for k in [1..nreg] do 
            e := e * 5 + img[k]; 
        end for;
        if best lt 0 or e lt best then best := e; end if;
    end for;
    return best;
end function;

//This function gives an explicit set of subsets of {1...n} that realizes 
// the vector of venn multiplicities m
function realize(m)
    lab := [{Integers() | }, {Integers() | }, {Integers() | },
            {Integers() | }];
    nx := 1;
    for k in [1..nreg] do
        for c in [1..m[k]] do
            for z in regions[k] do lab[z] := lab[z] join {nx}; end for;
            nx := nx + 1;
        end for;
    end for;
    return lab;
end function;

seen := AssociativeArray();
reps := [];
for m in types do
    ck := canonkey(m);
    if not IsDefined(seen, ck) then
        seen[ck] := true;
        lab := realize(m);
        Append(~reps, lab);
    end if;
end for;

// symmetric difference of the labels of size >= 2.  The sign characters
// force the coefficient to vanish unless this is empty.
function bigdelta(lab)
    D := {Integers() | };
    for Z in lab do
        if #Z ge 2 then D := D sdiff Z; end if;
    end for;
    return D;
end function;

if SYMBOLIC_N then
    printf "n is a FORMAL VARIABLE: the check runs in Q(n).\n";
else
    printf "n = %o,   dim A = %o\n", n, n + Binomial(n,2) + Binomial(n,4);
end if;
printf "monomial orbits under S_n and a<->b  : %o\n", #reps;
printf "setup time: %o s\n\n", Cputime(t_start);

/* =====================================================================
   7.  MAIN CHECK
   ===================================================================== */
bad := [];
active := 0;
for idx in [1..#reps] do
    lab := reps[idx];
    P1 := lab[1]; P2 := lab[2]; Q1 := lab[3]; Q2 := lab[4];
    lhs := norton_side(P1, P2, Q1, Q2);
    rhs := squares_side(P1, P2, Q1, Q2);
    if lhs ne 0 or rhs ne 0 then 
        active := active + 1; 
    end if;
    if lhs ne rhs then
        Append(~bad, lab);
        printf "FAILURE at %o | %o | %o | %o\n", P1, P2, Q1, Q2;
        printf "  norton  = %o\n", lhs;
        printf "  squares = %o\n", rhs;
    end if;
    if VERBOSE then
        printf "  %o | %o | %o | %o  ->  %o\n", P1, P2, Q1, Q2,
               (lhs eq rhs) select "ok" else "FAIL";
    end if;
end for;

printf "orbits inspected                : %o\n", #reps;
printf "  nonzero on each side          : %o\n", active;
printf "  trivially 0 = 0               : %o\n", #reps - active;
printf "mismatches                      : %o\n", #bad;
printf "total time                      : %o s\n", Cputime(t_start);
if #bad ne 0 then
    printf "\nIDENTITY FAILS.\n";
elif SYMBOLIC_N then
    printf "\n2n*eps(a^2 b^2 - (ab)^2) EQUALS the given combination as an\n";
    printf "identity of rational functions in n, hence for every n >= 7.\n";
    printf "The type-4 weight is 5-6(n-5)/(n-2) = (20-n)/(n-2): positive\n";
    printf "for n < 20, zero at n = 20 (that family drops out), negative\n";
    printf "for n > 20 (still an identity, no longer a sum of squares).\n";
else
    printf "\n2n*eps(a^2 b^2 - (ab)^2) EQUALS the given combination, n = %o.\n",
           n;
end if;

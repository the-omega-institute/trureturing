[Index](../marked_head_profile.md) · [Fixed-source factorial transport](128-the-complete-factorial-tail-retains-its-head-off-the-face.md) · [Quadratic costs](131-ten-complete-quadratic-costs-share-their-actual-off-face-head.md) · [Slot correction](133-unchanged-source-budgets-can-move-the-best-five-slot.md) · [Uniform source geometry](134-one-complete-cost-is-uniform-on-a-nonzero-k-neighborhood.md)

# The complete factorial tail is uniform on a source neighborhood

For every actual source in134's neighborhood

    qK>=1-sigma, sigma<=1/10000,
    rho<=1/100000, r<=1/520,

and every independently labelled complete original357 test A,

    integral Phi5(A)dmu
       <=5651735052209128490647/6560562600000000000000
        =0.861471095818692... <9/10,              (UF1)
    Phi5(v)=(v-5)_+*(v-4)/2.

Both K orientations and every feasible root1 beta distribution are
included. More precisely, the construction below retains a bound
Jbar(ell) for each original six-head layout, and a common complete
pair term Pbar, with

    integral Phi5(A)dmu<=Jbar(ell_A)+Pbar.         (UF2)

At zero radius every component recovers128/112, giving619/720.
The head dependence in(UF2) permits joint use with positive quadratic
expansions as in131. The present result does not evaluate those ten
combined costs or replace the current global inventory. It is an
ordinary continuum inequality with exact arithmetic, not a Lean
or unrestricted Erdős #7 result.

## 1. Uniform tables are bounds on one actual source

Use134's radius parameters delta,rho0,rbar,g,v0,v1,kbar,Cbar,cbar,Hbar.
All references below are to its canonical K orientation; the other
one is the same root0-cell exchange. Let p*,eta*,U*,w* be the128 face
pre-cap, ternary mass, rectangle-cap and density tables at q5=q15=0.
The exact exclusions are P everywhere, A in root1 and B in the actual
first-beta cell L, relabelled2.

Define

    eta_bar=((1+delta)/18,1/9,1/9,1/9,1/9),
    pbar_(c,j)=p*_(c,j) except in Q,
    pbar_(c,Q)=p*_(c,Q)+(v0 if c<2 else v1),
    dbar_(c,j)=eta_bar_c on allowed entries,0 on exclusions,
    Ubar_(c,j)=eta_bar_c*pbar_(c,j).              (UF3)

Here dbar is the descendant table, not the source availability d_c.
The bounds from116 and134 give componentwise

    p<=pbar, descendant<=dbar, U<=Ubar.

These are outer tables. They are not asserted to be the data of an
actual source, and no realizability or invented source record is used.
The whole-beta scope follows from116's beta-independent cap table;
the actual first-beta cell is retained under the relabeling.

The actual packing budget gives q5+q15<=rho0/g as well as the raw
upper bound2/5. Put qsum=min(2/5,rho0/g). Since actual carrier scores
satisfy0<=t0<=2delta and1-delta<=t_c<=1+delta for c!=0,

    wlo_(c,j)=max(0,w*_(c,j)-(2delta/5 if c=0 else delta/5)),
    whi_(c,j)=min(1,w*_(c,j)+(delta/5 if c!=0 else0)
                                      +qsum*I_(j=H)).       (UF4)

Every actual retained density obeys wlo<=w<=whi. Indeed the two
wrong-slot additions are nonnegative, are supported in H, and their
sum is at most qsum; the actual density itself is at most1. Dropping
the root restriction on q15 only enlarges the upper bound.

## 2. The bounded head retains the actual27 exclusion

133's signed slot identity provides lower pure5 masses

    qlo=(0,max(0,1/5-delta/4),max(0,1/5-delta/4),
           3/20,max(0,1/5-2rbar)).               (UF5)

The Q entry uses p,deltaA,deltaB,deltaH>=0; the H entry uses
r/h<=2rbar. Thus the actual q_j is at least qlo_j. No assertion that
its source parameters determine q_j is made.

For128's forced27 defect, the uniform bounds are

    e27<=(z-D)/135+Cbar*E27
         <=delta/360+Cbar*rho0=:ebar27.          (UF6)

On a reference-cell1 rectangle, write its surviving ideal credit as
(q_j/135-e27)_+. This is increasing in q_j and decreasing in e27.
Consequently the uniform rectangle cap is

    Hbar_(c,j)=min(Ubar_(c,j),
       max(0,whi_(c,j)*Ubar_(c,j)
                -I_(c=1)*(qlo_j/135-ebar27)_+ +rho0)).      (UF7)

This follows directly from128's single-rectangle inequality. It does
not apply a positive-measure argument to its signed reference.
As in128, the bounded-head term is zero unless

    r3=ROOT(c9)=r15, s5=s15,
    c45=c9, s45=s5.

Under this full compatibility it equals Hbar_(c9,s5). The tests keep
their original labels and their independent choices of residues.

## 3. A positive excess controls the entire old cross term

For the same actual source and density w, define

    nu=(mu-w*Lambda)_+.

128 proves nu(1)<=omega<=rho0 and nu<=(1-w)*Lambda. For the bounded
cell-slot function h=(B-4)_+, put M=max h<=2. Define128's five raw
coefficient operators C3,C5,C15,C45,Cmix using pbar,dbar from(UF3).
They are monotone on nonnegative inputs. Let

    b_i=C_i(whi*h), H_i=C_i((1-wlo)*h), e=M*rho0.

Then the complete old cross term is at most

    b3/18+(b5+b15+b45)/20+bmix/72
       +sum_(a>=3)min(e,H3*3^-a)
       +sum_(b>=2)sum_(i=5,15,45)min(e,Hi*5^-b)
       +sum_(a>=3,b>=1)min(e,Hmix*3^-a*5^-b).    (UF8)

For each original cylinder, its positive excess has both the common
mass bound e and its corresponding decaying cap. The coefficients
are valid because w<=whi,1-w<=1-wlo and the source tables are bounded
componentwise. This does not split rho among unrelated measures.
It uses one actual nu, with a conservative radius bound on its mass.

Every series in(UF8) is evaluated by128's exact complete formulas.
For the double series, sum the finitely many pre-crossing rows and
then the product of both remaining geometric tails. At e=0 all excess
terms vanish. No finite exponent cutoff is substituted for a tail.

## 4. The positive-seven cross term retains fixed rectangles

The complete raw row of128 is monotone in its three nonnegative
source coefficients. Its uniform version is

    Sbar_(c,j)=6Ubar_(c,j)+pbar_(c,j)/9
                 +3dbar_(c,j)/20+I_(dbar_(c,j)>0)/360.       (UF9)

The zero entries are the exact original-source exclusions at every
point of the neighborhood. Thus the final indicator does not acquire
a discontinuous new support near the face. Apply h<=I45+I3*I9*I5*I15:

    C7bar(ell)=[Sbar_(c45,s45)
                 +I_(r3=ROOT(c9)=r15,s5=s15)*Sbar_(c9,s5)]/5.

Add this term, the compatible bounded-head term(UF7), and(UF8).
Their sum is Jbar(ell). All three use the same original layout.

## 5. Complete distinct-pair tails have nonnegative prices

For the O-by-O pair part, use134's four cbar,Hbar reference envelopes
and the uniform family error masses

    e3=kbar*rho0, e5=rho0+delta/240,
    e1=ec=rho0.

The assigned cap in each family is

    cbar*p^-n+min(e_family,Hbar*p^-n).

Multiply by the original nonnegative LCM multiplicities from128:
2a-6 for pure3,2b-4 for pure5,6b-10 for root-five and10b-16 for
cell-five. Divide the resulting complete pure sum plus the unchanged
complete mixed sum by2. This defines POO_bar. The mixed coefficients
are raw Haar caps and require no source transport.

For the other two pair parts, the complete raw coefficients in128
are bounded respectively by

    (s,N3,N9,D,h,h1,max eta,deep mixed)
      <=(1/4+delta/2,5/36+delta/2,1/12+delta/2,
          3/4+delta/4,1/2+delta/18,1/3,1/9,1).    (UF10)

The first three use106's ||n-n*||1<=delta/2; all projected K beta
faces have s*=1/4,N3*=5/36,N9*=1/12. The remaining bounds are134's
source inequalities. The O-by-positive7 multiplicities are
nonnegative, so componentwise substitution directly gives PO7_bar.

For positive7-by-positive7 pairs, combine the diagonal subtraction
before bounding. At the old-coordinate LCM(a,b) its raw-cap price is

    (2/15)*(2a+1)*(2b+1)-1/10>=1/30>0.           (UF11)

Therefore all raw coefficients in(UF10) may again be replaced by
their upper bounds. This gives P77_bar. Equivalently, one may compute
(4Qraw_bar/15-Lraw_bar/5)/2 using the same assigned cap series, because
(UF11) has already justified its monotonicity. Subtracting an
independently bounded unknown moment would not justify this step.

Finally Pbar=POO_bar+PO7_bar+P77_bar. All multiplicity-weighted tails
are summed exactly, including their entire linear-times-geometric
continuations. Applying128's pointwise factorial inequality proves
(UF2). This proof imposes no relation among independent test residues.

## 6. Exact recovery, verification and remaining integration

At delta=rho0=0, all tables, densities, slot lower bounds and error
masses recover their face values. Thus Jbar(ell)=J112(ell) for every
one of12500 original heads, and Pbar=2539/3600. Maximization gives
139/900+2539/3600=619/720.

At the nonzero radius in(UF1), exact maximization gives its displayed
rational bound. The construction retains Jbar per head through the
`UniformFactorialHead.components` interface. A consumer can therefore
insert theta*Jbar into the same head maximum as its positive hinges,
and theta*Pbar into its head-independent complete term. Taking the
separate maximum in(UF1) earlier is also valid, but loses this coupling.
The method uses a radius envelope; it does not claim the sharper
seven-coordinate allocation retained for linear costs in134.

[uniform_factorial_neighborhood.py](../frontier/uniform_factorial_neighborhood.py)
and its [certificate](../certificates/source_norms/uniform_factorial_neighborhood.json)
check25000 original-head rows at the face and the nonzero radius,
including componentwise recovery and componentwise domination of the
actual height12 source. Its complete pair terms are also compared
with that actual-source computation. The ordinary bounds above supply
the continuum quantifier, not extrapolation from the finite example.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/uniform_factorial_neighborhood.py --check
```

This closes the source-uniform factorial input on the stated box.
Combining it with all required costs, the complete survival denominator
and the remaining source regions is a separate unresolved obligation.

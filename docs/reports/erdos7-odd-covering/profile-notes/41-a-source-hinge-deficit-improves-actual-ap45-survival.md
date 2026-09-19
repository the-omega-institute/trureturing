[Index](../marked_head_profile.md) · [Common actual mass](39-source-deficits-through-one-actual-survivor-mass.md) · [Fixed-barrier boundary](40-source-barrier-saturation-leaves-a-structural-gap.md)

# A source hinge deficit improves actual AP45 survival

On the complete actual AP11/T4,AP13/T5 law, retaining the signed source
remainder for h_(5/2)(v)=(v-5/2)+ gives

    J <= 257922307098126854721964898721072235577636047/602691118477933411109744202902940015336000
      =427.95106679105686...,
    Gamma13 <= 1339218237228092139323/9074811537787275423
             =147.5753222699582...,
    T13(81) <= 2873884370396495734788444926897322493/30159644293601482087441992044941875
            =95.28906715276494...,
    J+T13(81) <= 2928270257334924039784732959883529767674833273/5596417528723667388876196169813014428120000
              =523.2401339438218...,
    rho_actual >= 46826819251/94485352500
               =0.49559871463674754... .

The numerator costs, source-square norm Gnorm=102715/2916, square
comparison barrier45, and41 globally fixed linear barriers are those of
profile39. The stronger denominator uses the same actual source mass
and all original forbidden residues. All finite exponent heights and
complete geometric tails remain covered. The result is an ordinary
proof with exact rational verification, not a Lean theorem or a
negative-Q conclusion.

## A complete source inequality for the fractional hinge

Let f(v)=(v-5/2)+ and C=7/2. For the original zero7 block, the complete
auxiliary7 law has p1=29/35 and p_n=36/(5*7^n) for n>=2. Its centered
cost is

    psi(v)=sum_(n>=1)(p_n/n)[f(nv)-f(n)]
          =(29/35)f(v)+(18/245)f(2v)+(6/245)(v-1).

This identity holds at every integer v>=1: on n>=3 both hinge arguments
are in their affine range, and the entire tail has mass6/245. In
particular

    psi(1)=0,
    psi(2)=33/245,
    psi(v)=v-1117/490 for every integer v>=3.

There is no finite-height truncation. For b=1,2,3 the original cost
increments v_b=f(b+1)-f(b) are0,1/2,1. The source increments pay them:

    Delta psi(b)-Delta f(b)=33/245,3/35,0,

and the difference remains0 above3. The three-original-event floor
requires

    C>=max_(b=1,2,3)[f(b)+3*Delta f(b)]
      =max(0,3/2,7/2)=7/2.

Thus this hinge admits the same complete three-event source/deletion
comparison as the affine costs of profile39.

Fix one original test and its independent zero5 and first-positive5
ternary layouts b,c. On cell l put

    k_l=C-f(b_l),
    v_l=f(b_l+1)-f(b_l),
    t_l=c_l*v_l.

The original5,15,45 indicators have their own mod5 residues; their
ternary carriers are respectively the whole carrier, c's root and c's
cell. If N is their active count on cell l, then0<=N<=c_l and the same
original zero7 test A0 satisfies A0>=b_l+N. Discrete convexity and the
barrier inequality give

    (C-f(A0))_+ <= k_l-v_l*N,
    0<=t_l<=k_l.

No residues of independent tests are identified. The argument bounds
each complete original h_(5/2) test uniformly, as required by the later
AP survival comparison.

## Retain the same first-positive5 block through the whole tail

Use the actual raw pure3 measure eta and let x=sum_l eta_l. Let R2(c)
be the complete pure3 upper bound for integral psi(2*B1) with its original
baseline c. Let L_c be the corresponding complete first-moment bound
for B1 and L=max_c L_c. The complete positive5 comparison retains the
same B1 once in every n-strip Jensen sum. With p5_n=4/5^n for n>=2,
its general expression is

    P_c=sum_(n>=2)(p5_n/n)[R_n(c)-psi(n)*x
                              +(n-2)(R_n-psi(n)*x)]
          +x*sum_(n>=2)p5_n*psi(n),
    R_n=max_c R_n(c).

The only pre-affine strip is n=2. On n>=3, psi(nv)=nv-1117/490,
so the complete affine-tail identities are

    T0=sum_(n>=3)p5_n=1/25,
    T1=sum_(n>=3)n*p5_n=13/100,
    sum_(n>=2)p5_n*psi(n)=1479/24500.

The retained source contribution consequently has the exact closed form

    P_c=(2/25)*R2(c)+(1/25)*L_c+(1/20)*L-(99/2450)*x.

The negative last term is an exact affine centering term. The coefficients
of the source envelopes are nonnegative. Replacing retained R_n(c),L_c
by independent maxima recovers the preceding complete positive5 source;
there is no extra curvature correction for this affine-tail hinge.

## Source enlargement pays the same deleted events once

Let lambda35 be the raw actual35 measure, with cell masses n_l, and eta
its actual pure3 measure. For each of the three selected events, denote
its ternary carrier by D_e, original mod5 residue by J_e, full event by
I_e, and actual pure5 mass by h_e<=1/5. Define

    K_e(E)=integral_(D_e intersect E) v d eta,
    R_e(E)=h_e*K_e(E)-integral_E v*1_(I_e) d lambda35>=0.

Because Delta psi>=Delta f, enlarging the actual positive5 increment
to the pure product loses at least sum_e R_e. Expanding the selected
caps from h_e to1/5 then loses at least sum_e(1/5-h_e)K_e. With all
caps restored, the selected source upper bound U_bc therefore satisfies

    actual_selected_source
      <=U_bc-sum_e[(1/5-h_e)K_e+R_e].

These are two distinct steps of the same source comparison. The
zero7 source coefficient for this hinge is1. Its five selected pure3
cofactors have multiplicity at most5; the complete positive7 caps sum
to at most1/5. The weighted deleted intersections are therefore paid
by each R_e once, and the remaining h_e coefficient is nonnegative.
After adding source and deletion, setting h_e=1/5 gives the correction
t_l*eta_l/5. No independence of the actual event indicators is used.

Write a_l=k_l*n_l-t_l*eta_l/5, q_l=k_l*d_l-t_l/5, w_l=9*eta_l*k_l,
and R(z)=max(sum_(l<2)z_l,sum_(l>=2)z_l). The complete cap is

    W_bc=max(0,R(a))+max(0,a_0,...,a_4)
          +(13/243)*max(q)+(1/486)*max_l(k_l*d_l)
          +(sum(w)+R(w)+max(w))/36+max(k)/72.

The two zero alternatives cover empty shallow carriers. All deep signs
are safe: d_l>=1/4 and t_l<=k_l imply q_l>=k_l/20>=0. The selected
three deep coefficients sum to13/243, and1/486 covers the entire
remaining pure3 tail. Positive5 cofactor terms retain their complete
bounds.

Let U_bc now include the unchanged other original7 blocks, the selected
zero5 baseline terms, and P_c. Define

    m25(theta)=min_(b,c)[C*s-U_bc-W_bc/5].

Its underlying signed inequality is

    s*E_M[(f(A)-C)1_(Bmix^c)]<=-m25(theta).

Here M is the product of the actual normalized35 law and the actual
pure7 survivor law, and Bmix is their actual mixed7 forbidden union.
Let S=s*M(Bmix^c)>=D>0 and nu357=M(.|Bmix^c), exactly as in profile39.
Dividing only at this stage proves, for every complete original test,

    E_nu357 h_(5/2)(A)<=C-m25(theta)/S.

The margin is separately concave. The exact cancellation of the selected
zero7 summand leaves a positive sum of unchanged source envelopes, not
an arbitrary difference of convex functions. The retained P_c is a
positive sum of convex envelopes plus an affine term; W_bc is a maximum
expression with nonnegative tail coefficients. For fixed b,c the margin
is separately concave, and its finite minimum over independent layouts
preserves that property.

## The new survival denominator keeps the actual mass S

The physical AP11/T4,AP13/T5 union estimate of profile35 is

    rho_actual>=q0-H4/6-(4/33)*H5-H_(5/2)/22,
    q0=919/924.

The two earlier hinges retain their pre-deletion raw bounds
H4<=B4/S and H5<=B5/S. Substituting the new signed source inequality
for the third hinge gives

    rho_actual>=qeff-Bnew/S,
    qeff=q0-C/22=193/231,
    Bbase=B4/6+(4/33)*B5,
    Bnew=Bbase-m25/22.

This pays the full constant C/22=7/44; the source margin is not an
additional rebate applied to an independently normalized law. Define

    Delta_new=qeff*D-Bbase+m25/22.

The signed quantity Bnew need not be assumed nonnegative. Its separate
convexity follows because B4,B5 are separately convex and m25 is
separately concave. No monotonicity of a quotient in S is inferred from
its name or sign.

For a proposed uniform survival lower bound r, require qeff-r>=0 and

    (qeff-r)*D-Bbase+m25/22>=0.                       (R)

Replacing D by S increases this expression, so(R) gives
rho_actual>=r on the actual law. Its left side is separately concave;
all1296 vertex inequalities extend to the continuous parameter domain.
The reported r is positive, and qeff-r=32115488249/94485352500>0. Thus the
actual conditioning denominator qeff*S-Bnew is positive throughout.

At each of the six controlling vertices, the new hinge comparison has

    m25=3608083/23814000,
    B_(5/2)=167753/441000,
    C*D-m25=4331371/11907000.

The raw hinge decrease there is101/6075, so Delta_new exceeds its
preceding value by101/133650 after the AP weight1/22. These are exact
control-point identities. The global result follows from the new
fixed-target inequalities, not from assuming this gain at every theta.

## Four cost targets and survival extend on the same domain

Keep the profile39 numerator constants and raw deficits:

    H=AC*H16+H41,
    M=AC*Mq+Ml,
    N_J=H*S-M,
    N_Gamma=H16*S-Mq,
    N_T=A81*S+Raw81-cG*mg,
    N_K=(H+A81)*S+Raw81-M-cG*mg.

Here mg uses square barrier45; Raw81 retains all its internal s terms.
The complete source law and original test inventories are unchanged.
The cost upper numerators dominate the relevant nonnegative actual
expectations. Since the new conditioning denominator is positive, each
is divided by qeff*S-Bnew.

For target values Jstar,GammaStar,Tstar,Kstar, put
j=Jstar-C0, g=GammaStar-16 and k=Kstar-C0. Require j,g,Tstar,k>=0
and nonnegative D coefficients

    aJ=qeff*j-H,
    aGamma=qeff*g-H16,
    aT=qeff*Tstar-A81,
    aK=qeff*k-H-A81.

The sufficient target margins are

    aJ*D-j*Bbase+(j/22)*m25+M>=0,
    aGamma*D-g*Bbase+(g/22)*m25+Mq>=0,
    aT*D-Tstar*Bbase+(Tstar/22)*m25-Raw81+cG*mg>=0,
    aK*D-k*Bbase+(k/22)*m25-Raw81+M+cG*mg>=0.

All coefficients of concave source deficits are nonnegative, and all
subtracted raw source envelopes have nonnegative multipliers. Each
margin is separately concave. Their positive D coefficients justify
S>=D exactly as for(R), even if Bnew is signed.

At the reported targets, the coefficients aJ,aGamma,aT,aK are
approximately127.9695090,42.6538039,78.2646027,206.2341117; the verifier
checks their exact rational signs. Together with(R), there are6480
fixed-target vertex checks. The profile39 inherited source-margin tables
remain valid lower bounds for their globally defined separately concave
functions; the new positive coefficients permit using those lower bounds.
No concavity is claimed for a table patched with inherited entries.

All five extrema are attained by the bounding expressions at the same
six vertices398,410,422,616,628,640. Thus the reported Kstar equals
Jstar+Tstar exactly; there is no additional common-parameter sum gain
in this certificate.

## Other source branches, finite cores and the remaining gap

The eight missing3 or ineffective9 source branches retain their own
complete source and survival comparisons. They are checked separately
with the new uniform Gamma13, and lie below all reported main cost
targets. Their survival bounds exceed the reported r. The actual19
physical input remains nu13 K17, and both complete finite-core error
interfaces are recomputed on that law.

For box20/current8, the complete error is0.0005870917890972235... . The safe
separate joint allowance is307.710345. The common-sum
sufficient criterion is Kstar+error<403; its current excess is

    Kstar+error-403=120.24072103561092...>0.

Negative Q, arbitrary later-prime continuation and unrestricted
Erdos#7 remain open. Profile40's constant-only limit fixes the preceding
survival input; the present bound changes that input and does not
contradict its stated boundary. All extrema concern certified comparison
expressions, not attainment by actual congruence families.

## Exact reconstruction

The [verifier](../frontier/verify_survival_hinge_deficit.py) reconstructs
profile39's complete source, quadratic and linear profiles, checks their
margin hashes, and reproduces its entire consumer before adding this
hinge. It then checks all129600 new original-layout margins, the complete
positive5 and7 tail identities,6480 target vertex margins, all eight
fallback branches and both complete core interfaces. The
[certificate](../certificates/source_norms/survival_hinge_deficit.json)
records exact values and current dependency hashes.

Run:

    python3 docs/reports/erdos7-odd-covering/frontier/verify_survival_hinge_deficit.py --check

Default and `--check` only reconstruct and compare. Explicit `--write`
regenerates the certificate. These exact arithmetic checks support the
ordinary source/deletion and separate-concavity proof above; they do
not assert Lean verification or a frozen truth state.

[Index](../../marked_head_profile.md) · [Pure-three projection](../119-the-complete-pure-three-family-has-one-projected-defect.md) · [Root spill](../120-one-pure-three-defect-controls-root-spill-and-three-head-credits.md) · [Forced27 defect](../121-the-original-forced27-exclusion-has-a-quantitative-defect.md) · [Signed E5 rows](227-the-actual-deletion-mask-rows-have-one-off-face-error-budget.md)

# The complete pure-three projection shares the deletion-row budget

The inherited E3 deletion constraints and all three common-survivor link
families admit one signed error bound together with227's E5 constraints.
This covers883 priced rows, using the same actual source, original labels
and seven-coordinate defect budget. It remains a partial row-transport
result: the other raw/selected constraints, mass equalities, retained labels,
complete objective/tail and every scan alternative still require transport.
No complete off-face K bound is asserted here.

## 1. Split the original family before pricing its errors

Use195/208's two complete source domains and their canonical K orientation.
Let V27 be the complete virtual forbidden family27*7^e, e>=1, and V4 the
complete family3^a*7^e, a>=4,e>=1. Their disjoint defects are E27 and Ege4.
Let q be the actual pure-five survivor measure, z=q(1), D=max_c d_c and
DeltaD=z-D. The positive projected measures

    Xi27=q/135-(V27)^5>=0,
    Xi4=q/270-(V4)^5>=0

have exact total masses

    Xi27(1)=E27+DeltaD/135,
    Xi4(1)=Ege4+DeltaD/270.                         (JT1)

These use the projection of the whole original27 family. No restriction
to its good cell is made. For each original ternary depth-a cylinder J
and five-measurable F,119's product domination gives

    Lambda(J times F)<=3^-a*q(F).

Summing all positive seven depths, with weights6/(5*7^e), gives(JT1).
Their complete weights are1/5, and the later ternary sum is1/54.
Absent labels have zero actual mass and retain their entire nominal
defect. Independent residues and arbitrary depths are preserved.

Write B0,B1 for the original27 mass in cell0 and root1, and R1 for the
V4 mass in root1. The actual cell1 part of V4 is denoted V4,1. With e_c,s
for the actual deep-pure3 deletion in cell c and five slot s,

    e_0,s+e_1,s=q_s/90-Xi27_s-Xi4_s-B1_s-R1_s,
    e_1,s=q_s/135-Xi27_s-B0_s-B1_s+(V4,1)_s.       (JT2)

Thus the root0 row total is not the whole five projection. Subtracting
root1 with the equality's original signed price is essential.

## 2. Signed prices of the twenty-five E3 rows

Let q*=(0,1/5,1/5,3/20,1/5), in slots P,A,B,Q,H. In216 the five root0
row equalities have prices alpha_s, the five lower inequalities
-e_1,s<=-q*_s/135 have nonnegative prices beta_s, and the fifteen root1
zero rows have nonnegative prices gamma_c,s. Their actual priced residual is

    R3=sum_s alpha_s*(e_0,s+e_1,s-q*_s/90)
          +sum_s beta_s*(q*_s/135-e_1,s)
          +sum_(c>=2,s) gamma_c,s*e_c,s.

Insert(JT2) and discard only the nonpositive contribution
-sum_s beta_s*(V4,1)_s. This yields

    R3<=Sq+integral(beta-alpha)dXi27+integral(-alpha)dXi4
             +integral beta dB0
             +integral(gamma-alpha+beta)dB1
             +integral(gamma-alpha)dR1,
    Sq=sum_s k_s*(q_s-q*_s), k_s=alpha_s/90-beta_s/135. (JT3)

The forced P slot is empty for q and all these dominated measures, so it
can be omitted from every following supremum. Define

    xi=max_(s!=P)(beta_s-alpha_s)_+,
    chi=max_(s!=P)(-alpha_s)_+,
    b0=max_(s!=P) beta_s,
    b1=max_(c>=2,s!=P)(gamma_c,s-alpha_s+beta_s)_+,
    b4=max_(c>=2,s!=P)(gamma_c,s-alpha_s)_+.

The published original-label spill bounds give

    B0(1)<=(Cbar-1)*E27,cell0,
    B1(1)<=tbar*E27,root1,
    R1(1)<=tbar*Ege4,root1.

Here the two E27 subfamilies have disjoint original labels and their
sum is at most E27. Summing their prices before enlarging gives

    L27=xi+max((Cbar-1)*b0,tbar*b1),
    L4=chi+tbar*b4,
    R3<=Sq+DeltaD*(xi/135+chi/270)+L27*E27+L4*Ege4. (JT4)

No second copy of E27 is charged. The domain constants are
(tbar,Cbar)=(21/8,122/29) and(13/4,370/81), respectively.

For comparison, restricting the ideal27 reference to cell1 gives the
valid but no smaller price

    xi+max((Cbar-1)*max_s(xi+alpha_s)_+,
                    tbar*max_(c>=2,s)(xi+gamma_c,s)).

Indeed xi+alpha_s>=beta_s and xi+gamma_c,s>=gamma_c,s-alpha_s+beta_s.
The full projection removes this loss without an additional hypothesis.

## 3. Source-slot movement has an explicit signed bound

Let p,a,b be the existing nonnegative source losses. Let uA,uB,uH be the
pure-five tail deletions in A,B,H outside P. Packing gives

    0<=uA<=a, 0<=uB<=b,
    0<=uH<=min(r/h,r1/h1,(r-r1)/h0),
    uA+uB+uH<=1/20-p.

The exact slot identity is

    q-q*=(0,-uA,-uB,p+uA+uB+uH,-uH),
    Sq=k_Q*p+(k_Q-k_A)*uA+(k_Q-k_B)*uB+(k_Q-k_H)*uH. (JT5)

The identity follows by distributing the complete pure-five tail of
mass1/20-p over the four surviving first slots. In particular all five
coordinates share the same p and the same tail; they are not unrelated
variation errors.

On sigma<=d, source concentration gives p,a,b<=d/4. The support estimate
used in195 also gives p+a+b<=3d/[4(3-2d)]. Put

    g=( (k_Q)_+, (k_Q-k_A)_+, (k_Q-k_B)_+ ),
    Cq=min((d/4)*sum g, [3d/(4*(3-2d))]*max g).

Since h>=1/2 and r<=5Y1, where Y1=E5-G*q5,

    Sq<=Cq+10*(k_Q-k_H)_+*Y1.                       (JT6)

Both arguments inside the minimum are whole-domain upper bounds for
the first three terms of(JT5). This minimum requires no vertex claim
about a varying feasible set. Keeping the additional tail-cap inequality
can further improve it by a three-variable fractional-knapsack problem;
the present certificate uses only(JT6).

Finally DeltaD<=3sigma/8 gives the combined E3 source payment

    C3=Cq+d*(xi/360+chi/720).                        (JT7)

Its remaining prices are10*(k_Q-k_H)_+ on Y1, L27 on E27 and L4 on Ege4.

## 4. Three link families test one common overlap measure

Keep227's actual virtual deep-five measure z5, the full deep-pure3
measure z3, and W=V-delta>=0, W(1)=omega. For an old cell/slot/mask atom
C_i write x_i=Lambda(C_i), y_i=mu(C_i). Each of the three face link
families has the valid actual residual bound

    y_i-w*_i*x_i <= Dw_i*x_i+W(C_i),
    y_i+z5(C_i)-w*_i*x_i <= Dw_i*x_i+W(C_i),
    sum_(i in node)(y_i+z5(C_i)+z3(C_i)-w*_i*x_i)
                    <=sum_(i in node)Dw_i*x_i+W(node),           (JT8)

where Dw=wbar-w* is208's nonnegative upper-density increment. The last
line uses the original coarse E3/E5 link. All families dropped from V
are nonnegative and distinct as original labels; projected supports
need not be disjoint.

Let l_i,m_i,n_node be the nonnegative prices of these three links.
Their sum uses the pointwise coefficient

    u_i=l_i+m_i+n_node(i).

Consequently its W charge is at most(max_i u_i)*omega and its raw
payment is bounded by the fixed25-node raw polytope Pbar of208:

    Hu(q5,q15)=max_(X in Pbar) sum_node [max_(i in node)u_i]
          *[(d/5)*I_(c!=0)+q5*I_H+q15*I_(root1,H)]*X_node.       (JT9)

Taking three independent maxima first would discard the actual common
price field. The implementation adds them before either supremum.
The extra E3 rows(JT3) use virtual deletion, so they introduce no further
W price.

## 5. Combine primitive prices before spending the residual

Use exactly the existing seven coordinates

    Y=(E5-G*q5,E15-G*q15,E27,Ege4,E5d,E15d,omega),
    Y>=0, sum Y<=rho-G*(q5+q15).

From227 take its signed E5/H/support source coefficient C5 and primitive
prices, substituting the combined u_i in its link contribution. Add(JT6)
and(JT4) to their corresponding coordinates before taking the largest
price L. These883 rows then have the whole-domain bound

    d*C5+C3+max_(q in {(0,0),(rho/G,0),(0,rho/G)})
                    [Hu(q)+(rho-G*(q5+q15))*L].                 (JT10)

The source and residual are the same actual ones in every term.
Pbar is fixed while the objective in(JT9) is affine in q, so Hu is convex.
This proves the three-vertex bound in(JT10). It does not establish
convexity of a retained LP whose constraint matrix depends on q.

## 6. Exact finite price consumer and its scope

The [helper](../../frontier/transport/joint_deletion_row_transport.py) checks the
physical rows in both original223 branches. It retains227's433 priced
rows and25 exact mask-aggregation identities, adds400 old survivor links,
25 coarse links, and25 E3 constraints. It verifies195/208's original
domain guards and evaluates(JT10) for all2060 stored rational223 duals.
The [certificate](../../certificates/source_norms/retained-transport/joint_deletion_row_transport.json)
contains the exact domain maxima, hashes of all computed prices and
both complete heavy controllers' component prices and raw LP witnesses.
Split inputs use the existing semantic certificate IO.

| Whole source domain | Maximum883-row error bound |
| --- | ---: |
| sigma<=1/20, rho<=1/1000 | 0.7560333453137374 |
| sigma<=1/12, rho<=1/3000 | 0.42724561744335754 |

The result includes more rows than227, so these numbers are not a
replacement for its smaller five-group charges. They price exactly the
stated joint contribution. They must not be added to a face optimum and
reported as a complete off-face objective.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/joint_deletion_row_transport.py --check
```

Other original raw/selected margins and caps, mass equalities, the new
135/125 rows, all omitted tails, and every complete-scan pruning candidate
remain separate obligations. No new global comparison, Lean verification
or unrestricted covering result is asserted.

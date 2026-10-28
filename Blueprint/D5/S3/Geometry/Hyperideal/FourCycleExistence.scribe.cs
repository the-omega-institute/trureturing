using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every four-cycle incidence system has one shared interior zero-curvature vector.",
        H("A simultaneous solution for all global edge equations"),
        Blocks(
            Paragraph(Text("Let T be a finite type of tetrahedra and E a type of global edge labels "
                + "with decidable equality. The incidence s assigns a label to each of the six local "
                + "edges of every tetrahedron and a low/high colour to each global label. "
                + "FourCycle(s) requires the four low slots to form the prescribed local cycle, "
                + "degree eight at each low label, and degree at least twelve at each high label. "
                + "Degrees are actual fibre cardinalities, including repeated occurrences.")),
            Paragraph(Text("The lower and upper endpoints L(s) and U(s), local cosine C(s,x,o), "
                + "and curvature K(s,x,e) are exactly those of FourCycleCurvature. "
                + "In particular, each local coordinate reads the same global vector x:E -> Real. "
                + "K is 2pi minus the sum of arccos(C) over the actual occurrence fibre.")),
            Describe.Lean(
                DescribeId.Create("fourcycle-shared-zero-curvature"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/FourCycleExistence.fourcycle_zero_curvature"),
                H("An interior vector with all angle sums equal to 2pi"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every global label has a nonempty finite occurrence fibre, "
                        + "so the incidence map is surjective and the edge-label type is finite. "
                        + "This finiteness is derived from FourCycle(s); it is not an additional hypothesis.")),
                    Paragraph(Text("The established box has strictly positive radicands, "
                        + "strictly admissible cosines, and inward curvature margins on all faces. "
                        + "Polynomial operations, square roots away from zero, division and arccos "
                        + "make the actual shared curvature map continuous on this box.")),
                    Paragraph(Text("Normalize the box to a unit cube. The cube is a retract of "
                        + "a simplex: divide its n coordinates by n+1, append the slack coordinate "
                        + "one minus their sum, and project back by multiplying the n non-slack weights "
                        + "by n+1 and clamping to [0,1]. The classical simplex fixed-point theorem "
                        + "therefore applies to the clamped curvature self-map. Strict face signs "
                        + "exclude every boundary coordinate of its fixed point; interior clamp "
                        + "cancellation then forces every curvature to vanish.")),
                    Paragraph(Text("The conclusion concerns the real incidence system. "
                        + "It does not assert that arbitrary incidence data form a manifold, "
                        + "supply face pairings or vertex-link conditions, or prove unrestricted CFMP. "
                        + "The geometric interpretation of the cosine formula and the passage to "
                        + "a complete hyperbolic realization retain their separate hypotheses."))),
                DescribeRole.Theorem),
            Paragraph(Text("The original FourCycle hypotheses also give a forward "
                + "degree-normalized curvature flow converging to the shared zero. No separate "
                + "finite-edge, inward-sign or equilibrium hypothesis is needed. Retain the "
                + "original local edge order (12,13,14,34,24,23) and the actual occurrence "
                + "degrees d_e=degree(s,e), including repetitions. Positive degrees make the "
                + "occurrence map onto E, so finite T again implies finite E.")),
            Paragraph(Text("Pass from the established cosh box to its actual length box: "
                + "a_e=arcosh(L(s,e)), b_e=arcosh(U(s,e)), and B_s=[a,b]. Its lower "
                + "length bounds are strictly positive because 1<L(s,e). For a single "
                + "global length vector p define K_e(p)=curvature(s,cosh(p),e), with cosh "
                + "applied coordinatewise. The existing fourcycle_zero_curvature supplies "
                + "one x* strictly inside the same cosh box; c_e=arcosh(x*_e) lies strictly "
                + "inside B_s and satisfies K(c)=0. Monotonicity of cosh on nonnegative "
                + "lengths and cosh(arcosh(L))=L, cosh(arcosh(U))=U transport the original "
                + "box inequalities and strict face-curvature signs exactly.")),
            Paragraph(Text("For each tetrahedron t let R_t(p)_q=p_(s.edge(t,q)), and use "
                + "the compact six-length family C_s=union_t R_t(B_s). It is the finite "
                + "union of continuous images of the same compact global box. Every read "
                + "is positive and satisfies the original strict cosine inequalities by "
                + "fourcycle_curvature_box applied to cosh(p). Thus this family consists "
                + "of genuine local lengths. Shared labels always read the same p; neither "
                + "this construction nor the curvature sums replace repeated occurrences "
                + "with independent coordinates.")),
            Paragraph(Text("Apply the actual normalized-flow construction to C_s, B_s "
                + "and c. The positive angle-Jacobian estimate on the compact family, "
                + "occurrence-counted incidence sums, and degree-weighted strong "
                + "antimonotonicity supply a constant mu>0. The transferred strict face "
                + "signs give box invariance, and the uniform local-to-global ODE pasting "
                + "gives a forward solution for every initial value in B_s. This selects "
                + "one c and one mu before quantifying over the initial value. The rate "
                + "may depend on s through C_s; this statement supplies no rate uniform "
                + "over the size or geometry of all FourCycle systems.")),
            Paragraph(Text("Explicitly, for each x0 in B_s there is a trajectory "
                + "n:Real -> (E -> Real) with n(0)=x0 such that for every t>=0, "
                + "n(t) belongs to B_s and n'_e(t)=K_e(n(t))/d_e. The derivative assertion "
                + "also holds at t=0. With D(t)=sqrt(sum_e d_e*(n_e(t)-c_e)^2), "
                + "the degree-weighted Gronwall estimate gives "
                + "D(t)<=exp(-mu*t)*D(0). Strong antimonotonicity also shows that c is "
                + "the unique zero of K within B_s.")),
            Paragraph(Text("These trajectories converge to c as t tends to positive "
                + "infinity. Indeed d_e>=1 gives |n_e(t)-c_e|<=D(t) for every e and hence "
                + "the finite-product sup norm is bounded by D(t). Since mu>0, the "
                + "exponential upper bound tends to zero. This establishes convergence "
                + "of the whole vector in the finite-product topology, without identifying "
                + "its default sup norm with the displayed weighted Euclidean distance.")),
            Paragraph(Text("Forward uniqueness also holds on this same box. Two "
                + "trajectories satisfying the displayed box and derivative conditions "
                + "with the same value at t=0 coincide for every t>=0. The corresponding "
                + "uniqueness statement also holds for two box trajectories satisfying "
                + "the multiplicative equation n'_e=n_e*K_e(n), with its derivative "
                + "condition at t=0 included. These are separate applications to the "
                + "two specified vector fields.")),
            Paragraph(Text("The original strict cosine inequalities and positive "
                + "radicands make every local arccos branch smooth near each box point. "
                + "Finite occurrence sums therefore make the actual K continuously "
                + "differentiable there, as are K_e/d_e and p_e*K_e. The derivative of "
                + "each field has a finite bound on the compact box. Its convexity "
                + "then gives a Lipschitz bound on that same box. Applied on each "
                + "interval [0,t] to the two supplied box trajectories, the ODE "
                + "Gronwall estimate bounds their distance by their zero initial "
                + "distance times exp(L*t), forcing equality. No face-sign, "
                + "equilibrium or spectral premise is added to this uniqueness argument.")),
            Paragraph(Text("The multiplicative flow also exists and converges on the "
                + "same original FourCycle length box, with the same shared zero c. Choose "
                + "constants 0<a0<=a_e and b_e<=b0 with b0>0 for every label; finiteness "
                + "and strict positivity of the box endpoints supply these constants. "
                + "If E is empty choose a0=b0=1; all sums and trajectory comparisons "
                + "then have their empty-product meanings. The constants are selected "
                + "before the initial value, and all reads retain the original incidence "
                + "and occurrence multiplicities.")),
            Paragraph(Text("For x,c>0 define h(c,x)=x-c-c*log(x/c). The elementary "
                + "logarithm bound log(y)<=y-1, applied at sqrt(x/c) and c/x, gives "
                + "(sqrt(x)-sqrt(c))^2<=h(c,x)<=(x-c)^2/x. Consequently, for "
                + "a0<=x,c<=b0, one has h(c,x)>=0, a0*h(c,x)<=(x-c)^2 and "
                + "(x-c)^2<=4*b0*h(c,x). For the last inequality factor x-c as "
                + "(sqrt(x)-sqrt(c))*(sqrt(x)+sqrt(c)) and bound the second "
                + "factor squared by 4*b0.")),
            Paragraph(Text("The same strict face signs and smooth local curvature "
                + "branches give, for every x0 in B_s, a forward trajectory p with "
                + "p(0)=x0, p(t) in B_s and p'_e(t)=p_e(t)*K_e(p(t)) for t>=0, "
                + "including the derivative at zero. Set H(t)=sum_e h(c_e,p_e(t)) "
                + "and Q(t)=sum_e d_e*(p_e(t)-c_e)^2. Since d_e>=1, the scalar "
                + "bounds give a0*H(t)<=Q(t). Differentiating h in x gives 1-c/x, "
                + "so the positive multiplicative factor cancels and "
                + "H'(t)=sum_e (p_e(t)-c_e)*K_e(p(t)). The same compact-family "
                + "strong antimonotonicity and K(c)=0 imply "
                + "H'(t)<=-mu*Q(t)<=-mu*a0*H(t).")),
            Paragraph(Text("The scalar Gronwall inequality now yields "
                + "H(t)<=H(0)*exp(-mu*a0*t). Moreover each squared coordinate "
                + "error is at most 4*b0*H(t), because each nonnegative entropy "
                + "summand is at most H(t). Hence the finite-product sup norm "
                + "of p(t)-c is at most sqrt(4*b0*H(t)), which tends to zero. "
                + "Thus the actual multiplicative flow converges to c for every "
                + "initial value in B_s. This entropy rate may depend on s and "
                + "does not provide a rate uniform over all FourCycle systems.")),
            Paragraph(Text("These applications establish both analytic flows on the "
                + "concrete FourCycle length box. Forward uniqueness compares "
                + "trajectories that remain in this box. Physical Schlaefli and "
                + "co-volume identifications, face isometries, manifold and link "
                + "conditions, and conclusions outside this box retain their "
                + "separate obligations.")),
            Paragraph(Text("The same four-cycle box also permits an arbitrary prescribed raw "
                + "curvature vector kappa:E -> Real with |kappa(e)|<eta for every global label, "
                + "where eta is the exact positive FourCycleCurvature.margin. The incidence, "
                + "colouring, fibre degrees, endpoints L(s), U(s), and occurrence-counted "
                + "curvature K(s,x,e) are unchanged. Finiteness of E follows from the actual "
                + "positive fibre degrees as above; no independent finite-edge or solution "
                + "assumption is added.")),
            Paragraph(Text("For normalized cube coordinates u, use the same affine box map "
                + "X(u)_e=L(s,e)+(U(s,e)-L(s,e))*u_e and clamp the increment "
                + "u_e+K(s,X(u),e)-kappa(e) to [0,1]. Positive radicands and nonzero "
                + "denominators, polynomial and square-root continuity, continuous arccos, "
                + "finite occurrence sums, and the continuous min/max clamp make this map "
                + "continuous. On a lower face, "
                + "K-kappa>=eta-kappa(e)>0; on an upper face, "
                + "K-kappa<=-eta-kappa(e)<0. The two strict inequalities use the two sides "
                + "of |kappa(e)|<eta. The existing cube fixed-point and clamp arguments "
                + "therefore exclude every boundary coordinate and give K(s,X(u),e)=kappa(e) "
                + "for every global label at one shared fixed point.")),
            Paragraph(Text("Consequently one shared vector x lies strictly between the original "
                + "lower and upper endpoints at every global label, every original local "
                + "cosine remains strictly between -1 and 1, and every raw curvature equals "
                + "its prescribed component. Repeated occurrences and repeated labels still "
                + "read that same x. The admissible curvature bound eta is independent of "
                + "the number of tetrahedra, while the original high-edge lower floor can "
                + "depend on that number; this does not supply a uniform spectral bound.")),
            Paragraph(Text("This is an application of the established analytic box and "
                + "fixed-point machinery. Identifying x with cosh of native edge lengths, "
                + "identifying the raw angle with the native dihedral angle, constructing "
                + "paired face isometries, and proving edge and truncation-endpoint cone "
                + "charts retain their separate geometric obligations. A nonzero prescribed "
                + "raw defect is not by itself a constructed native cone metric.")),
            Paragraph(Text("An actual-adjacency certificate gives a further application to "
                + "the original Incidence s with finite T and finite E, with decidable equality "
                + "on E. Choose an arbitrary global upper vector b:E -> Real satisfying "
                + "1<b_e<=2 for every e. The field s.low remains part of Incidence, but this "
                + "application imposes no colouring condition, FourCycle(s), or degree premise. "
                + "Its hypothesis will instead be a strict angle-sum certificate on each "
                + "actual occurrence star.")),
            Paragraph(Text("Keep the original local order (12,13,14,34,24,23), numbered "
                + "0 through 5. For o=(t,i), write e_j=coordinate(s,o,j)=s.edge(t,frame(i,j)). "
                + "The six rows of frame, in order, are [0,1,2,3,4,5], [1,2,0,4,5,3], "
                + "[2,1,0,5,4,3], [3,1,5,0,4,2], [4,5,0,1,2,3], and [5,4,0,2,1,3]. "
                + "Thus e_0=source(s,o) is the target label, e_3 is its opposite label, "
                + "and e_1,e_2,e_4,e_5 are its adjacent labels. The star(s,e) consists of "
                + "all pairs o with source(s,o)=e; degree(s,e) is its cardinality. Distinct "
                + "pairs remain distinct summands even when their global labels coincide.")),
            Paragraph(Text("Write c(r,y,z,p,v,w) for the original FourCycleEnvelopes.cosine. "
                + "With `rad(r,y,w)=2*r*y*w+r^2+y^2+w^2-1`, its exact expression is "
                + "`(y*z+v*w+r*y*v+r*z*w-(r^2-1)*p)` divided by "
                + "`sqrt(rad(r,y,w))*sqrt(rad(r,z,v))`. Define "
                + "u(s,b,o)=c(b_(e_0),b_(e_1),b_(e_2),1,b_(e_4),b_(e_5)) and "
                + "S_e(b)=sum_(o in star(s,e)) arccos(u(s,b,o)). Assume S_e(b)>2pi "
                + "for every global label e. Every displayed b entry reads the same global "
                + "vector, retaining all repeated adjacent and target labels. The opposite "
                + "argument 1 is a conservative independent-coordinate comparison endpoint. "
                + "If the opposite label also occurs in another slot, assigning 1 to that "
                + "argument does not assert a simultaneous global assignment or a native "
                + "tetrahedron realizing the comparison tuple.")),
            Paragraph(Text("The mixed comparison cosine_mixed_comparison does not decrease c when "
                + "the four adjacent arguments increase and the opposite argument decreases, "
                + "with the target fixed. For all six arguments in [1,2], it gives "
                + "c(r,1,1,2,1,1)<=c(r,y,z,p,v,w)<=c(r,2,2,1,2,2). "
                + "Here rad(r,1,1)=(r+1)^2 and `rad(r,2,2)=(r+1)*(r+7)`; evaluating "
                + "the numerators and cancelling positive factors gives the explicit bounds "
                + "`2*(2-r)/(r+1)<=c(r,y,z,p,v,w)<=(9-r)/(7+r)`. "
                + "For 1<r<=2 the lower bound is nonnegative and the upper bound is "
                + "strictly less than 1, since 9-r<7+r. In particular 0<=u(s,b,o)<1. "
                + "These range bounds are consequences of the formula, not extra certificate hypotheses.")),
            Paragraph(Text("Put N=card(T x Fin 6) and `g(t)=N*arccos(2*(2-t)/(t+1))`. "
                + "The denominator is nonzero at t=1, so continuity of arccos gives "
                + "continuity of g there, and `g(1)=N*arccos(1)=0<2pi`. Hence g(t)<2pi "
                + "throughout a neighbourhood of 1. Each strict inequality 1<b_e gives "
                + "a neighbourhood on which t<b_e. Intersect these finitely many "
                + "neighbourhoods and the condition t<2 with the first neighbourhood; "
                + "the intersection contains an interval (l,r) with l<1<r. Taking "
                + "a=(1+r)/2 gives one common floor with 1<a<2, a<b_e for every e, "
                + "and `N*arccos(2*(2-a)/(a+1))<2pi`. This construction requires no "
                + "maximum of an empty collection of degrees.")),
            Paragraph(Text("Consider the global box a<=x_e<=b_e and put "
                + "`theta=arccos(2*(2-a)/(a+1))>=0`. Every local coordinate lies in "
                + "(1,2], so the preceding bounds give 0<=C(s,x,o)<1, in particular "
                + "the original strict bounds -1<C(s,x,o)<1, on the whole closed box. "
                + "On the lower face x_e=a, every o in star(s,e) has e_0=e. The lower "
                + "comparison therefore gives `2*(2-a)/(a+1)<=C(s,x,o)`, and the "
                + "decreasing function arccos gives angle(s,x,o)<=theta. Consequently "
                + "`sum_(o in star(s,e)) angle(s,x,o)<=degree(s,e)*theta<=N*theta<2pi`. "
                + "The middle inequality uses star(s,e) as a subset of T x Fin 6 and "
                + "theta>=0. Thus K(s,x,e)>0 on every lower face.")),
            Paragraph(Text("On the upper face x_e=b_e, fix an occurrence o in star(s,e). "
                + "Its target is b_(e_0)=b_e. For j=1,2,4,5 the box gives x_(e_j)<=b_(e_j), "
                + "while x_(e_3)>=a>1. The same mixed comparison now yields "
                + "C(s,x,o)<=c(b_(e_0),b_(e_1),b_(e_2),1,b_(e_4),b_(e_5))=u(s,b,o). "
                + "Thus arccos(u(s,b,o))<=angle(s,x,o), and summing the actual occurrences "
                + "gives sum_(o in star(s,e)) angle(s,x,o)>=S_e(b)>2pi. Hence "
                + "K(s,x,e)<0 on every upper face. Label coincidences preserve each "
                + "coordinate inequality and every summand, so both face estimates apply "
                + "to the original shared-variable system.")),
            Paragraph(Text("To apply the same fixed-point machinery, put n=card E, choose "
                + "an enumeration q:E -> Fin n with inverse, and normalize by "
                + "`X(z)_e=a+(b_e-a)*z_(q(e))` for z in [0,1]^n. The positive widths "
                + "b_e-a send this cube into the global box. Define the endomap "
                + "G(z)_i=max(0,min(1,z_i+K(s,X(z),q^(-1)(i)))). The min/max expression "
                + "takes values in [0,1]. For arguments at least 1, rad is strictly "
                + "positive: the three squares are at least 1 and the product term "
                + "is nonnegative, so rad>=2. Polynomial and square-root continuity "
                + "and the nonzero square-root denominators make each local cosine "
                + "continuous on the box. Continuous arccos, the finite occurrence sums, "
                + "and continuous min/max then make G a continuous cube endomap.")),
            Paragraph(Text("The original cube_fixed_point argument in FourCycleExistence, "
                + "supplied by the simplex theorem Brouwer through the cube retraction, "
                + "gives one vector z with G(z)=z. Fix any e only after choosing this z. "
                + "Its q(e)-coordinate satisfies max(0,min(1,t+v))=t, with "
                + "t=z_(q(e)) and v=K(s,X(z),e). If t=0, then X(z)_e=a and v>0, "
                + "so the clamped value is positive, contradicting t=0. If t=1, "
                + "then X(z)_e=b_e and v<0, so the clamped value is less than 1, "
                + "again a contradiction. For 0<t<1 neither endpoint can be the "
                + "clamped value; cancellation gives t+v=t and v=0. This is exactly "
                + "the original clamp_fixed_zero argument.")),
            Paragraph(Text("Set x=X(z) for that one fixed point. Simultaneously for all "
                + "global labels, a<x_e<b_e and K(s,x,e)=0; for every original local "
                + "occurrence, -1<C(s,x,o)<1. All angle sums equal 2pi at this same "
                + "global interior vector. No per-edge choice of separate solutions "
                + "enters the argument. The finite intersection and the cube argument "
                + "also allow empty finite types. If an edge label has an empty star, "
                + "however, its S_e(b)=0 violates the assumed strict certificate.")),
            Paragraph(Text("This conditional application assumes the certificate for every "
                + "actual star; it does not establish it for any particular nonempty "
                + "incidence system. Its conclusion concerns the original raw cosine, "
                + "angle and curvature formulas. Interpreting ell_e=arccosh(x_e) as native lengths "
                + "still requires the native hyperideal tetrahedron realization and "
                + "the identification of these arccos values with its dihedral angles. "
                + "Compatible face isometries, the original face-pairing quotient, "
                + "manifold and vertex-link conditions, and complete hyperbolic gluing "
                + "with totally geodesic boundary remain separate geometric obligations. "
                + "The argument uses the existing fixed-point route; it does not supply "
                + "the Schlaefli/co-volume minimization argument, Ricci-flow existence "
                + "or convergence, uniqueness, or completion of the full sections 1-125.")),
            Paragraph(Text("For a finite nonempty block set T and a finite global label set E, "
                + "let Q(t,i), i in Fin 4, read four coordinates from one vector ell:E -> Real. "
                + "The native six local occurrences have labels "
                + "[Q(t,0),Q(t,2),Q(t,3),Q(t,1),Q(t,2),Q(t,3)]. "
                + "Assume this actual six-occurrence map is surjective. Repeated labels remain "
                + "separate occurrences. With local coordinates ordered [r,o,a,b], the native "
                + "angle field is Phi=[theta_r,theta_o,2 theta_a,2 theta_b]; the factors two "
                + "account for the repeated transverse occurrences.")),
            Paragraph(Text("Choose an initial native angle quadruple u_t satisfying strict B4 "
                + "for every block: all four entries are positive, u_r+u_a+u_b<pi, and "
                + "u_o+u_a+u_b<pi. Write b_t=[u_r,u_o,2u_a,2u_b]. "
                + "The positive native right inverse supplies local comparison lengths for "
                + "these targets. These comparison lengths belong to individual blocks; "
                + "their existence imposes no simultaneous global length assignment.")),
            Paragraph(Text("Let m_t be the minimum of the four positive entries and the two "
                + "positive B4 triangle margins, and take eps=(min_t m_t)/4. This one eps "
                + "is positive for the finite nonempty family. Perturb each weighted target "
                + "coordinate by plus or minus eps. In the native angle quadruple, a transverse "
                + "coordinate changes by half that amount. All eight perturbations remain in "
                + "strict B4. Applying the native right inverse gives nonnegative local vectors "
                + "Y(t,i,s) with Phi(Y(t,i,s))=b_t plus or minus eps times the i-th coordinate vector.")),
            Paragraph(Text("For all x,y in Real^4, (Phi(x)-Phi(y)) dot (x-y)>=0. "
                + "The native field is componentwise nonnegative and vanishes in its own coordinate whenever "
                + "that length coordinate is nonpositive. For each block, bound all eight "
                + "comparison dot-products by C_t=sum_(i,s)|Phi(Y(t,i,s)) dot Y(t,i,s)|. "
                + "The finite-witness estimate then gives eps times the local sup norm, "
                + "minus C_t, as a lower bound for (Phi(x)-b_t) dot x.")),
            Paragraph(Text("Define F(ell)_e by summing Phi(readout_Q(ell,t))_i-b_(t,i) "
                + "over every local position with Q(t,i)=e. Every summand reads the same ell. "
                + "Surjectivity ensures every global coordinate occurs in a block, so its "
                + "sup norm is at most the sum of the local readout norms. Finite-sum "
                + "reindexing gives F(ell) dot ell=sum_t (Phi(readout_Q(ell,t))-b_t) dot "
                + "readout_Q(ell,t), and consequently eps norm(ell)-C <= F(ell) dot ell "
                + "with C=sum_t C_t. Independent comparison witnesses are used only in this estimate.")),
            Paragraph(Text("The field F is continuous. Suppose it has no zero and put "
                + "R=C/eps+1. Normalize the cube [-R,R]^E to [0,1]^E and use the "
                + "self-map G_j=(1-F(ell)_j/norm(F(ell)))/2. The coordinate norm bound "
                + "puts G in the cube, and the assumed absence of zeros makes it continuous. "
                + "The same existing cube fixed-point supplier yields a point with "
                + "ell=-(R/norm(F(ell)))F(ell). Hence norm(ell)=R and F(ell) dot ell<=0, "
                + "whereas the outward estimate gives F(ell) dot ell>=eps R-C=eps>0. "
                + "This contradiction supplies one common zero of F.")),
            Paragraph(Text("Every target mass at a global label is strictly positive: "
                + "surjectivity supplies an actual occurrence and strict B4 supplies its "
                + "positive target. If ell_e<=0, each matching native field coordinate "
                + "vanishes, so F(ell)_e is minus this positive target mass. A zero of F "
                + "therefore has all global lengths strictly positive.")),
            Paragraph(Text("For the reciprocal-degree choice u_(t,i)=2pi/degree(Q(t,i)), "
                + "degree counts the original six-occurrence fibre. Summing its target "
                + "over that fibre gives exactly 2pi, with the two transverse repetitions "
                + "already present in Phi and b. At the common zero, the actual six-slot "
                + "extended native angle sum at every global label is consequently 2pi. "
                + "This specialization still requires strict B4 of every initial quadruple.")),
            Paragraph(Text("The reciprocal-degree specialization admits the following conditional "
                + "degree criterion. Put n=card T, m=card E, and let d(e) be the cardinality "
                + "of the fibre of e in the actual map T x Fin 6 -> E with labels "
                + "[Q(t,0),Q(t,2),Q(t,3),Q(t,1),Q(t,2),Q(t,3)]. Each pair (t,j) is "
                + "counted separately, including repeated labels within one block. Assume "
                + "this map is surjective, Q(t,2)=A and Q(t,3)=B for every t, and that "
                + "A, B, S are three pairwise distinct labels in E. Assume also m<n. "
                + "The two degree criteria below concern every label other than A and B.")),
            Paragraph(Text("Number the six occurrence slots from 0 to 5. The maps from "
                + "T x Fin 2 selecting slots 1 and 4 inject into the fibre of A; selecting "
                + "slots 2 and 5 gives an injection into the fibre of B. In each case, "
                + "equality of occurrence pairs recovers both the block and the selected slot. "
                + "Thus d(A)>=2n and d(B)>=2n, even when an axial slot also has label A or B. "
                + "The fibres over all labels partition T x Fin 6, so sum_(e in E) d(e)=6n. "
                + "Surjectivity makes every d(e) strictly positive.")),
            Paragraph(Text("The distinct labels A, B, S give 3<=m, and m<n therefore gives "
                + "n>=4. For either axial label e=Q(t,0) or e=Q(t,1), define the normalized "
                + "triangle budget R(e)=2/d(e)+2/d(A)+2/d(B). The common-label bounds "
                + "give 2/d(A)<=1/n and 2/d(B)<=1/n. If e is A or B, the axial term "
                + "is bounded by 1/n as well; its repeated appearance in R(e) remains "
                + "a separate term.")),
            Paragraph(Text("First assume d(e)>=4 for every e distinct from A and B. "
                + "When n>=5 and the axial label is A or B, R(e)<=3/n<=3/5<1. "
                + "For any other axial label, 2/d(e)<=1/2, so "
                + "R(e)<=1/2+2/n<=9/10<1. These estimates apply separately to both "
                + "Q(t,0) and Q(t,1).")),
            Paragraph(Text("For the remaining four-degree case n=4, the inequalities "
                + "3<=m<n force m=3. Hence A, B, S exhaust E, and the literal degree "
                + "mass becomes d(S)+d(A)+d(B)=24. The assumptions and injections give "
                + "d(S)>=4, d(A)>=8 and d(B)>=8. For an axial label S, these bounds give "
                + "R(S)<=1/2+1/4+1/4=1. Equality would force equality in all three "
                + "positive reciprocal bounds, hence d(S)=4, d(A)=8 and d(B)=8; their "
                + "sum would be 20, contradicting 24. Thus R(S)<1. If the axial label "
                + "is A or B, R(e)<=3/4<1. Exhaustion by the three labels covers both "
                + "axial slots, completing the four-degree criterion for every n>=4.")),
            Paragraph(Text("Independently, assume d(e)>=6 for every e distinct from A "
                + "and B. The same cardinality premise gives n>=4. For an axial label "
                + "A or B, R(e)<=3/n<=3/4<1; for any other axial label, "
                + "R(e)<=1/3+2/n<=5/6<1. This six-degree argument applies directly "
                + "to both axial slots for all n>=4, using no four-block endpoint "
                + "or three-label mass calculation.")),
            Paragraph(Text("Under either degree criterion, set u_(t,i)=2pi/d(Q(t,i)). "
                + "Surjectivity and pi>0 make all four entries positive. Multiplying "
                + "R(Q(t,0))<1 and R(Q(t,1))<1 by positive pi gives, respectively, "
                + "u_r+u_a+u_b<pi and u_o+u_a+u_b<pi, since Q(t,2)=A and Q(t,3)=B. "
                + "Thus every initial quadruple satisfies the strict B4 condition "
                + "required by the preceding common-length argument.")),
            Paragraph(Text("That argument supplies one global vector ell:E -> Real "
                + "with every ell_e>0 and F(ell)=0. Each occurrence in the fibre of e "
                + "has assigned target angle 2pi/d(e); its target sum is therefore "
                + "d(e) times 2pi/d(e)=2pi. The repeated transverse slots are exactly "
                + "the factors two in Phi and b. At F(ell)=0, the actual six-occurrence "
                + "extended native angle sum equals this assigned sum at every global "
                + "label. All these equalities use the same global vector ell.")),
            Paragraph(Text("These are conditional applications of the preceding "
                + "existence argument. The source cardinality inequality card E<card T "
                + "and the stated degree bounds remain premises; their extraction from "
                + "the original boundary Euler/genus assumptions is a separate obligation. "
                + "Applying the criteria to the original CFMP data also requires identifying "
                + "Q and its six-occurrence map with the actual face-pairing quotient, "
                + "including coverage and the three distinct labels. The genuine-angle "
                + "region, flat-block geometry and compatible complete hyperbolic gluing "
                + "retain their original geometric requirements.")),
            Paragraph(Text("This derivation applies the existing fixed-point machinery and "
                + "native analytic formulas under explicit hypotheses. It does not derive "
                + "the initial strict B4 condition from the original boundary Euler/genus "
                + "assumptions, identify arbitrary incidence data with the original face "
                + "quotient, or construct flat-block geometry and compatible hyperbolic gluing. "
                + "Strictly positive lengths alone do not establish that every block lies in the genuine-angle region. "
                + "Those geometric bridges are separate obligations of the original CFMP problem.")))));

    private static Formula Statement()
    {
        var t=F.Id("T"); var eType=F.Id("E"); var s=F.Id("s");
        var x=F.Id("x"); var e=F.Id("e"); var o=F.Id("o");
        var interior=All([("e",eType)],And(
            Lt(Apply(Call("L",s),e),Apply(x,e)),
            Lt(Apply(x,e),Apply(Call("U",s),e))));
        var cosine=Call("C",s,x,o);
        var strict=All([("o",Call("Product",t,Call("Fin",F.D(6))))],And(
            Lt(F.Seq(F.Minus,F.D(1)),cosine),Lt(cosine,F.D(1))));
        var zero=All([("e",eType)],Eq(Call("K",s,x,e),F.D(0)));
        var exists=new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"),
                new Formula.TypeArrow(eType,F.Id("Real")))],And(interior,strict,zero));
        return All([("T",F.Id("Type")),("E",F.Id("Type")),
            ("s",Call("Incidence",t,eType))],
            Imp(And(Call("Fintype",t),Call("DecidableEq",eType),Call("FourCycle",s)),exists));
    }

    private static Formula All((string Name,Formula Type)[] variables,Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula And(params Formula[] p)
    {
        if(p.Length==0) throw new ArgumentException("Empty conjunction");
        var q=p[^1]; for(var i=p.Length-2;i>=0;i--) q=new Formula.Logic(p[i],FormulaLogicOperator.And,q);
        return q;
    }
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Apply(Formula function,params Formula[] args)=>new Formula.Apply(function,[..args]);
    private static Formula Call(string name,params Formula[] args)=>Apply(F.Id(name),args);
}

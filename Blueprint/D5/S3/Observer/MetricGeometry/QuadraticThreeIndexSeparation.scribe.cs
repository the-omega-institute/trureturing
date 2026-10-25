using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class QuadraticThreeIndexSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two independently calibrated quadratic report families have an exact attained separation in the original three-coordinate supremum norm.",
        H("Exact Three-Index Quadratic Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-reports"),
                DeclarationHandle.Create(Prefix + "Reports"),
                H("Original observation space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reports is the space of all functions from Fin 3 to the real numbers, with the ordinary Pi norm: the maximum absolute value of the three coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-nodes"),
                DeclarationHandle.Create(Prefix + "nodes"),
                H("Three indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real u and v, nodes(u,v) has coordinates zero, u and v, in that order. The separation theorem restricts u and v to natural numbers with 1 <= u < v."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-report"),
                DeclarationHandle.Create(Prefix + "report"),
                H("Independently calibrated reports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real u,v,t,A,B and j in Fin 3, report(u,v,t,A,B)(j) is A times the square of nodes(u,v)(j)+t, plus B. A and B belong to this report's world; the other world has its own gain and offset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-right-coefficient"),
                DeclarationHandle.Create(Prefix + "kRight"),
                H("Right directional coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real u,v,r, kRight(u,v,r) equals u*v/(u+2*r) when r <= (v-u)/2, and u*(v-u)/(2*r) otherwise. On the theorem's domain r >= 0 and 0 < u < v, the denominators are positive in their respective branches. At r=(v-u)/2 both displayed value formulas agree."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-left-coefficient"),
                DeclarationHandle.Create(Prefix + "kLeft"),
                H("Left directional coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real u,v,r, kLeft(u,v,r) equals (v-u)*v/(v-u+2*r) when r <= u/2, and u*(v-u)/(2*r) otherwise. On the theorem's domain both branches have positive denominators. At r=u/2 both displayed value formulas agree. The internal spacing is reflected, so the two directional functions cannot be exchanged while keeping u fixed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-sharp-value"),
                DeclarationHandle.Create(Prefix + "sharpValue"),
                H("Sharp separation value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real u,v,m,s,t, put d=t-s, rR=max(s+v/2,0) and rL=max(-t-v/2,0). The value sharpValue(u,v,m,s,t) is m*d times the minimum of kRight(u,v,rR) and kLeft(u,v,rL)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-center"),
                DeclarationHandle.Create(Prefix + "center"),
                H("Exact offset from the full difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any three-coordinate real vector q, center(q) is minus one half of the sum of its largest and smallest coordinate. Both extrema use all three coordinates. In each attaining construction q is the full report(u,v,s,A,0)-report(u,v,t,A',0), including the constant quadratic terms. The offsets are exactly B=center(q) and B'=0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-distances"),
                DeclarationHandle.Create(Prefix + "distances"),
                H("All independently legal distances"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real u,v,m,s,t, distances(u,v,m,s,t) contains exactly the norms of report(u,v,s,A,B)-report(u,v,t,A',B') over all real A,A',B,B' with A >= m and A' >= m. The offsets are unrestricted and independent. Neither gain has an upper bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-attains"),
                DeclarationHandle.Create(Prefix + "Attains"),
                H("A prescribed finite pair attains"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real u,v,m,s,t,A,A', Attains asserts A >= m, A' >= m, and equality between sharpValue(u,v,m,s,t) and the norm of the two original reports with these gains and the exact offsets B=center(q), B'=0. It is a property of this particular gain pair, rather than an existentially selected alternative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-three-index-exact-separation"),
                DeclarationHandle.Create(Prefix + "quadratic_three_index_separation"),
                H("Least separation and all five finite attaining choices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let u,v be arbitrary natural numbers with 1 <= u < v, and let m,s,t be arbitrary real numbers with m > 0 and s < t. Put w=v-u, d=t-s, rR=max(s+v/2,0), rL=max(-t-v/2,0). The set distances(u,v,m,s,t) has least element m*d*min(kRight(u,v,rR),kLeft(u,v,rL)). Thus every independently legal four-parameter calibration has at least this distance, and a finite calibration has exactly this distance.")),
                    Paragraph(Text(
                        "The same theorem gives five separately accessible attaining implications. If s <= -v/2 <= t, take A=A'=m. If s > -v/2 and s+v/2 <= w/2, take A'=m and A=m*(1+d*2/(u+2*(s+v/2))). If s > -v/2 and w/2 <= s+v/2, take A'=m and A=m*(1+d/(s+v/2)). If t < -v/2 and -t-v/2 <= u/2, take A=m and A'=m*(1+d*2/(w+2*(-t-v/2))). If t < -v/2 and u/2 <= -t-v/2, take A=m and A'=m*(1+d/(-t-v/2)). Each implication asserts both gain inequalities and exact norm equality with its own full q and the offsets B=center(q), B'=0.")),
                    Paragraph(Text(
                        "Both inequalities at each directional junction are closed. Consequently both prescribed gain pairs attain there, although their gains generally differ. At the right junction rR=w/2 the two z values are 2/v and 2/w; at the left junction rL=u/2 they are 2/v and 2/u. The two formulas for the value agree at each junction. Contacts with the center are included in the first implication. Equal and unequal spacings and arbitrary signed origins are all included.")),
                    Paragraph(Text(
                        "For the right-hand lower bound write f=u*(u+2*s), g=v*(v+2*s), and e for the full original report difference. The exact cancellation identity (g-f)*e(0)-g*e(1)+f*e(2)=2*A'*(t-s)*u*v*(v-u) eliminates the other gain and both offsets. Each coordinate lies between minus and plus the Pi norm. When f <= 0 the absolute coefficient sum is 2*(g-f), and when f >= 0 it is 2*g. The resulting bounds use A' >= m. Across the center the endpoint difference gives the bound directly using both gain inequalities. Reflection of the original coordinates exchanges the worlds and replaces u by v-u, supplying the left-hand bound.")),
                    Paragraph(Text(
                        "For the two right-hand constructions, subtracting q(0) gives respectively the patterns (0,-2*c,-2*c) and (0,-2*c,0), where c is the corresponding sharp value. Centering the full q therefore gives norm at most c, and the universal lower bound gives equality. Reflection supplies both left-hand constructions; centering the original full q remains optimal among all offsets. These are conditional mathematical statements about the original reports. They require no prior interval, noise, injectivity of an auxiliary coordinate map, measurability, computability, estimator, risk or operational interpretation, and make no classification of all minimizing calibrations."))),
                DescribeRole.Theorem),
            Paragraph(Text("Original worlds and exact risk.")),
            Paragraph(Text("Fix natural indices 1 <= u < v, real endpoints a < b, a gain floor m > 0, and epsilon >= 0. Set w=v-u, L=b-a and c=2*epsilon/m. An original world consists of an origin t in [a,b], a finite real gain A >= m, an unrestricted finite real offset B, and a vector eta with |eta(j)| <= epsilon for every j in Fin 3. Its observation is report(u,v,t,A,B)+eta. The gain, offset and three noise coordinates can be chosen independently in each of two worlds. The decision is any total function from Reports to the real numbers, with no measurability or computability requirement.")),
            Paragraph(Text("Put d0=c/v, dR=c*(u+v+2*b)/(u*v+2*c), eR=c*(v+2*b)/(u*w+2*c), dL=c*(-u-2*a)/(v*w+2*c), and eL=c*(-v-2*a)/(u*w+2*c). Let Psi=max(d0,max(dR,max(eR,max(dL,eL)))) and D=min(L,Psi). All five denominators are strictly positive. Signed numerators are retained: a directional fraction can be negative, while d0 >= 0 ensures Psi >= 0. The infimum, over all decisions, of the supremum absolute error over all original legal worlds is D/2.")),
            Paragraph(Text("Actual placement of a fixed origin gap.")),
            Paragraph(Text("For a gap 0 <= d <= L, minimize the original report distance over all s,t in [a,b] with t-s=d and all independently legal gains and offsets. Write Q=u*v*w. The least distance is F(d)=m*Q*d/M(d), where M(d)=max(u*w,max(w*(u+v+2*b-2*d),max(v*(v+2*b-2*d),max(u*(-u-2*a-2*d),v*(-v-2*a-2*d))))). The maximum includes the positive constant u*w, so division is legitimate.")),
            Paragraph(Text("To locate the actual origins, define H_R(x)=max(u*w,max(w*(u+2*x),2*v*x)) and H_L(x)=max(u*w,max(u*(w+2*x),2*v*x)). The directional formulas give kRight(u,v,max(x,0))=Q/H_R(x) and kLeft(u,v,max(x,0))=Q/H_L(x). Both H functions are nondecreasing. For any s,t with gap d, H_R(s+v/2) <= H_R(b-d+v/2) and H_L(-t-v/2) <= H_L(-a-d-v/2). Hence the fixed-pair separation is at least F(d). If the first endpoint denominator is the larger one, take (s,t)=(b-d,b); otherwise take (s,t)=(a,a+d). The selected pair has denominator exactly M(d). The attained fixed-pair separation then supplies finite legal gains and offsets at this actual pair. At d=0 take s=t=a and identical calibrations.")),
            Paragraph(Text("For every real d, the positive-denominator inequality F(d) <= m*c is equivalent to Q*d <= c*M(d). Because c >= 0, multiplication distributes over this maximum. Splitting the resulting maximum into its five alternatives and cancelling the positive factors u,v,w gives exactly d <= d0 or d <= dR or d <= eR or d <= dL or d <= eL. Thus the feasible gaps in [0,L] have largest element D, and the endpoint construction attains a clean-report distance at most 2*epsilon at gap D.")),
            Paragraph(Text("Exact compatible origins in the original coordinates.")),
            Paragraph(Text("For any y in Reports, let C(y) be the set of t in [a,b] for which finite real A >= m and B satisfy |y(j)-report(u,v,t,A,B)(j)| <= epsilon at every original coordinate. This is exactly the set of origins of legal worlds whose observation is y: in one direction use the actual noise, and in the other set eta(j)=y(j)-report(u,v,t,A,B)(j). No independent error bounds on interpolation coefficients are introduced.")),
            Paragraph(Text("Use lambda=1/A, xi=2*t and omega=(A*t^2+B)/A. The compatible triples are exactly the closed linear constraints 0 <= lambda <= 1/m, 2*a <= xi <= 2*b, and |lambda*y(j)-nodes(u,v)(j)^2-xi*nodes(u,v)(j)-omega| <= epsilon*lambda for all j. These constraints cannot have lambda=0. The coordinate at zero would force omega=0; the other two coordinates would then give u*(u+xi)=0 and v*(v+xi)=0. Since 0 < u < v, they would force xi=-u=-v, a contradiction.")),
            Paragraph(Text("Conversely every feasible triple has lambda > 0 and realizes the finite legal original parameters A=1/lambda, t=xi/2 and B=omega/lambda-(1/lambda)*(xi/2)^2. Dividing each original-coordinate inequality by lambda yields the required original noise bound. Substituting the forward parameters proves the reverse inclusion. Therefore C(y) is exactly the image of this feasible set under the map taking a triple to xi/2.")),
            Paragraph(Text("The feasible set is closed and convex. It is bounded in a compact box: lambda and xi already have their displayed bounds, and the coordinate at zero gives |omega| <= (|y(0)|+epsilon)/m. Its linear xi/2 image is consequently compact and convex. Whenever y is obtainable, C(y) is nonempty and equals the closed interval from its infimum to its supremum, including a singleton when the two endpoints coincide.")),
            Paragraph(Text("Midpoint optimality and finite worlds at the lower bound.")),
            Paragraph(Text("If s,t belong to C(y), choose their compatible original clean reports. Coordinatewise triangle inequalities bound their distance by 2*epsilon. The least-distance placement and five-alternative inequality imply |s-t| <= D. For an obtainable y, write ell=inf C(y) and h=sup C(y). The decision (ell+h)/2 has conditional error exactly (h-ell)/2. Every other real answer z has max(|z-ell|,|z-h|) >= (h-ell)/2. Thus the midpoint minimizes the worst conditional absolute error, and its global error is at most D/2. On unobtainable reports any total definition is permitted.")),
            Paragraph(Text("At the extremal gap D, choose the actual endpoint placement and finite calibrations just described, with clean original reports p0 and p1. Their distance is at most 2*epsilon. Set the shared report to (p0+p1)/2 and the respective noise vectors to (p1-p0)/2 and (p0-p1)/2. Each coordinate has absolute value at most epsilon. The two legal worlds share exactly the same report and have origins s,t with t-s=D. Every decision returns one real answer there, and at least one of its two absolute errors is at least D/2. The compatible interval at that report is exactly [s,t]: it contains both origins, is an interval, and has diameter at most D. If D=0, choose one legal world twice; the same conclusions hold. In particular epsilon=0 remains included.")),
            Paragraph(Text("The supremum of the error for an arbitrary decision is allowed to be infinite. Equivalently, take the supremum of ENNReal.ofReal of the absolute error over every original legal world and then the infimum over decisions. The two-world inequality gives a lower bound for every decision in this complete lattice, while the midpoint gives a finite upper bound. Both bounds are ENNReal.ofReal(D/2), which identifies the ordinary finite minimax value without assuming that every decision has bounded error. The argument concerns this mathematical observation model and makes no empirical or worldwide originality claim.")),
            Paragraph(Text("Nonconstant budgets on acquired 013 and 023 fibers.")),
            Paragraph(Text("Set z=-3/2. Fix arbitrary real m>0, c>0 and c/3<E<=(1+c)/2. For j=13 use u=1,v=3, and for j=23 use u=2,v=3. For every real three-report history y, let C_j(y) consist of all t in [z-E,z+E] for which some finite real A>=m and B satisfy norm(y-report(u,3,t,A,B))<=m*c/2. A single A and B must satisfy all three original coordinate inequalities. This is exactly original-noise compatibility: the error vector is y-report(u,3,t,A,B), whose three entries are bounded by m*c/2. These histories can be acquired from one four-coordinate world; the fourth, unobserved error can be set to zero without further restricting this fiber.")),
            Paragraph(Text("Define P=c*(1+2*E)/(3+2*c), G=c*(1+E)/(3+c), chi=P-G, q=E-P, r=E-G, gamma=c/3 and h(x)=min(chi,max(r-x,0)). Then 0<q<r<E, r<=1/2, r-q=chi>0, and G=gamma*(1+r)=gamma+(1+2*gamma)*chi. Take any real coefficient 0<=beta<=min(1,gamma). Define rho_13(t)=G/2-beta*h(z-t) for t<=z, and rho_13(t)=(P-beta*chi)/2+beta*h(t-z) for t>z. Define rho_23(t)=rho_13(-3-t). The center belongs to the first branch in both designs. The elementary bounds 0<=h<=chi give G/2-beta*chi<=rho_j(t)<=(P+beta*chi)/2. Moreover G-2*beta*chi>=gamma+chi>gamma>0, so every radius is positive and uniformly bounded.")),
            Paragraph(Text("For any s<t in C_j(y), choose their jointly compatible calibrations. The norm triangle inequality gives norm(report(u,3,s,A,B)-report(u,3,t,A',B'))<=m*c. Apply quadratic_three_index_separation to these actual original reports. For design 013, writing d=y0-x0 for nonnegative distances x0<y0 from the center, the negative-side restriction is d<=gamma*(1+x0) when x0<=1/2 and d<=c*x0 otherwise. The positive-side restriction is 3*d<=c*(1+2*x0) when x0<=1 and d<=c*x0 otherwise. Across the center it is t-s<=gamma. Combining each one-sided restriction with d+x0<=E gives t-s<=P throughout the fiber and t-s<=G on its negative half. In the far negative branch, E<=(1+c)/2 and x0>1/2 give d<=E-x0<=G. In the far positive branch, the same prior bound and x0>1 give d<=E-x0<=P. Thus these restrictions include the closed directional junctions and do not replace original errors by independent difference errors.")),
            Paragraph(Text("To prove |s-t|<=rho_13(s)+rho_13(t), first take s=z-y0<t=z-x0<=z, with 0<=x0<y0<=E and d=y0-x0. If x0>=r, both tapers vanish and the radius sum is G. If x0<r, put w=r-x0>0; since x0<r<=1/2, the original separation bound gives d<=gamma*(1+x0)=G-gamma*w. For d<=chi, one has d+beta*(h(x0)+h(y0))<=(1+2*beta)*chi<=G-gamma<G. For d>chi, h(x0)+h(y0)<=w: when w<=chi, the first taper is w and the second is zero; when w>chi, the first is chi and max(w-d,0)<=w-chi bounds the second. Hence d+beta*(h(x0)+h(y0))<=G-gamma*w+beta*w<=G. Both cases are exactly the required negative-side radius inequality.")),
            Paragraph(Text("Next take z<s=z+x0<t=z+y0. If x0<=q, then h(x0)=chi and the two radii sum to P+beta*h(y0)>=P>=t-s. If x0>q, the clipping formula gives chi-h(x0)<=x0-q. Consequently the radius sum is at least P-beta*(x0-q)>=P-(x0-q)=E-x0>=t-s, using beta<=1 and the original prior. If s<=z<t, then t-s<=gamma, while the two radii sum to at least G-2*beta*chi>gamma. Equal origins follow from positive radii. These cases cover every pair in the 013 fiber, including the center and all taper endpoints.")),
            Paragraph(Text("For 023 reverse the three report coordinates and replace each origin t by -3-t, keeping the same gain and offset. The original quadratic reports and their original-coordinate noise bounds then coincide with those of 013 in reversed order. The symmetric prior is preserved. This exact correspondence and the definition of rho_23 give the same pairwise budget inequality on every 023 fiber. It relates two fixed histories and does not presume an extra observation.")),
            Paragraph(Text("For either design and any nonempty C=C_j(y), put L=sup{t-rho_j(t):t in C} and U=inf{t+rho_j(t):t in C}. The prior and uniform radius bounds make both sets nonempty and bounded. The pairwise budget inequality gives s-rho_j(s)<=t+rho_j(t) for every s,t in C, so the conditional supremum and infimum rules yield L<=U. For each t in C, t-rho_j(t)<=L<=(L+U)/2<=U<=t+rho_j(t). Thus d_j(y)=(L+U)/2 simultaneously satisfies |d_j(y)-t|<=rho_j(t) for every compatible origin. Set d_j(y)=z when C is empty. In particular beta=min(1,c/3) supplies the stronger budgets of Theorem 7.2 in the quadratic-clock private-randomization model. This is a conditional consequence of the exact separation theorem and real-order properties; it does not assert acquisition lawfulness, measurability, a randomized risk value or a matching minimax lower bound.")))));
}

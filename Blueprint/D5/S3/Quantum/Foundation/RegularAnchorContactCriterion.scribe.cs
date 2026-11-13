using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RegularAnchorContactCriterionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);

    public DocumentDefinition Create()
    {
        Formula r=Seq(Mathbb,Grp(V("R"))), space=V("V"), cone=V("C"), unit=V("u"),
            p=V("p"), e=V("e"), a=V("a"), n=V("n"), x=V("x");
        Formula dual=C("LinearMap",r,space,r), ball=C("closedBall",D(0),D(1)),
            radius=C("minimum",n), body=C("shell",n), distance=C("boundaryDistance",n);
        Formula contact=C("Nonempty",C("intersection",ball,C("frontier",body)));
        Formula strict=Imp(Seq(D(1),F.Lt,Sp,radius),And(
            C("subset",C("smul",radius,ball),body),And(
                C("subset",ball,C("interior",body)),And(
                    Le(Seq(radius,Minus,D(1)),distance),Seq(D(0),F.Lt,Sp,radius,Minus,D(1))))));
        Formula criterion=And(Iff(Eq(C("width",a),D(1)),Eq(radius,D(1))),
            And(Iff(Eq(radius,D(1)),contact),strict));
        Formula result=Ex("n",C("NativeChart",cone,unit,p,e,a),C("ContactCriterion",n));
        Formula quantified=All("p",C("pure",cone,unit),All("e",dual,
            Imp(C("common",cone,unit,p,e),Imp(C("Regular",cone,unit,p),
                All("a",C("FullBall3Chart",cone,unit,p),result)))));
        Formula hypotheses=Imp(C("IsClosed",cone),Imp(
            All("x",space,Imp(C("mem",x,cone),Imp(Seq(x,Neq,Sp,D(0)),
                Seq(D(0),F.Lt,Sp,C("apply",unit,x))))),Imp(
                    Eq(C("span",r,cone),C("top")),Imp(C("EB3",cone,unit),
                        Imp(C("exclusionInjective",cone,unit),quantified)))));
        Formula statement=All("V",V("Type"),Seq(
            OpenBracket,C("NormedAddCommGroup",space),CloseBracket,Sp,
            OpenBracket,C("NormedSpace",r,space),CloseBracket,Sp,
            OpenBracket,C("FiniteDimensional",r,space),CloseBracket,Sp,
            All("C",C("PointedCone",r,space),All("u",dual,hypotheses))));
        Formula definition=All("V",V("Type"),Seq(
            OpenBracket,C("NormedAddCommGroup",space),CloseBracket,Sp,
            OpenBracket,C("NormedSpace",r,space),CloseBracket,Sp,
            OpenBracket,C("FiniteDimensional",r,space),CloseBracket,Sp,
            All("C",C("PointedCone",r,space),All("u",dual,
                All("p",C("pure",cone,unit),All("e",dual,
                    All("a",C("FullBall3Chart",cone,unit,p),
                        All("n",C("NativeChart",cone,unit,p,e,a),
                            Iff(C("ContactCriterion",n),criterion)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The original regular-anchor system satisfies the complete width, minimum and actual shell-contact equivalence, with positive strict-scale distance.",
            H("Regular-anchor contact and shell scale"),Blocks(
        Paragraph(Text("Let V be a finite dimensional real normed space, C its original closed generating cone, and u a linear functional strictly positive on every nonzero vector in C. Keep the entire normalized base K, all its extreme points P, and the entire original effect interval zero <= f <= u. Every original exclusion D(p) is the image of the entire closed Euclidean three-ball under an injective affine map. Assume that equality of exclusion sets implies equality of their original pure labels. No closedness of P, pair properness, least-confirmation law, matrix representation or dimension reduction is assumed.")),
        Describe.Lean(DescribeId.Create("three-space"), DeclarationHandle.Create(Owner + "ThreeSpace"),
            H("Original coordinate space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The coordinate space is EuclideanSpace over the reals indexed by Fin 3, with its Euclidean inner product and norm."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("full-ball-chart"), DeclarationHandle.Create(Owner + "FullBall3Chart"),
            H("Entire exclusion chart"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A chart consists of an injective affine map a from the three-dimensional coordinate space to V whose image of the whole closed unit ball equals the original exclusion. Its center is c=a(0), and its linear part B is injective. The native chart conversion preserves the map and the exact whole-image equality."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("eb3"), DeclarationHandle.Create(Owner + "EB3"),
            H("All original exclusions are three-balls"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every pure point of the entire original base there exists a full three-ball chart. This quantifies every original label and every mixed state in its exclusion."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("native-chart"), DeclarationHandle.Create(Owner + "nativeChart"),
            H("Existing native chart carrier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The same affine map, injection and whole exclusion equality form an ExclusionChart with dimension exactly three."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("regular"), DeclarationHandle.Create(Owner + "Regular"),
            H("Original regularity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Regularity at p says that there exists exactly one original linear effect e confirming p and vanishing on every state of D(p). It is uniqueness in the entire common-confirmation family, rather than uniqueness of an exclusion label."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("normal-span"), DeclarationHandle.Create(Owner + "NormalSpan"),
            H("Signed original normal space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("N(p) is the existing zeroPositive set of all original linear functionals nonnegative on the whole cone and zero at p. NormalSpan is its real linear span. Neither positivity nor a choice of effects replaces this signed span."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coordinates"), DeclarationHandle.Create(Owner + "coordinates"),
            H("Actual constant and slope restriction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Restriction coordinates of f are its value at the chart center and the existing Euclidean Riesz slope of f composed with B. The exact native slope formula gives f(a(w))=f(c)+inner(slope(f),w) for every coordinate vector, including vectors outside the unit ball."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("affine-coordinates"), DeclarationHandle.Create(Owner + "affineCoordinates"),
            H("All affine coordinate functions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The standard constant-plus-linear equivalence for affine maps and the finite dimensional Riesz equivalence identify all affine real functions on the coordinate space with a real constant and a coordinate vector."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("native-laws"), DeclarationHandle.Create(Owner + "NativeChart"),
            H("Derived native chart laws"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The data include a linear equivalence from span N(p) onto all affine functions on the actual three-ball, with its forward map proved equal to original restriction. They include an original linear H:V->R^3 satisfying H(a(w))=w for all w, every coordinate functional of H in span N(p), and H(p)=0. For g=u-e they include g in N(p), g(a(w))=1, strict positivity of g on all K except p, and a finite positive M with norm(H(x))<=M*g(x) on the whole original cone. They also identify original comparison zero with the entire exclusion on K, prove source salience from the strict unit, prove u(Bw)=0 for all w, and give dim(span N(p))=4."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("regular-anchor-native"), DeclarationHandle.Create(Owner + "regular_anchor_native"),
            H("Original regular-anchor restriction and uniform bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Assume the original closed cone, strict unit, generation, full EB3, injective exclusion labels, an original pure p, its common confirmer e, actual regularity at p, and any full chart a of D(p). Then NativeChart data exist with exactly these original parameters. No restriction isomorphism, extension, positivity bound, support representation or shadow geometry is an input.")),
                Paragraph(Text("OriginalNormalRestriction.original_normal_restriction supplies the full affine restriction equivalence on the span of all positive continuous annihilators. Finite-dimensional linear-to-continuous equivalence transports that very span to NormalSpan. Its forward map is the original restriction, not a separately reproved bijection. The standard affine constant-plus-linear and Riesz equivalences give the actual constant and slope coordinates.")),
                Paragraph(Text("Pull back the three unit coordinate slopes to obtain H. Positive annihilators with slopes plus and minus r times each coordinate vector equal g plus and minus r times the corresponding coordinate functional of H. Whole-cone positivity gives absolute value of each H coordinate at most g/r; the Euclidean triangle inequality gives the finite bound M=3/r. Thus the bound includes every mixed original state and extends homogeneously to all cone vectors. For strict positivity of g on K except p, OriginalWidthContact.top_subsingleton_of_zero_exclusion applies to the same common effect e and proves that its entire maximum face is the singleton p.")),
                Paragraph(Text("ExclusionWidthCompactness.comparison_zero_iff identifies comparison(p,x)=0 with an actual original confirmer vanishing at x on the entire base, exactly the native exclusion definition. The construction establishes the original-domain input for normalized shadow ratios; width, directional support minima and boundary-distance conclusions require their additional arguments. These are consequences within the specified mathematical model; no physical realization or literature priority is asserted."))), DescribeRole.Theorem),
                Paragraph(Text("Application to the entire native qutrit family.")),
                Paragraph(Text("Take V=HermitianMat(Fin(3),C) with its existing real normed-space and finite-dimensional instances, C=HermitianExclusionKernel.cone, and u=HermitianExclusionKernel.unit, the real trace. This is the entire PSD cone and its whole trace-one base. HermitianMat.isClosed_nonneg proves closedness; HermitianMat.trace_pos gives strict positivity of u on every nonzero PSD element; the positive-part minus negative-part decomposition shows that this cone spans all of V.")),
                Paragraph(Text("The real Riesz equivalence represents every original real-linear functional f on V as X -> inner(E,X) for one Hermitian E. The original condition proper(C,u,f) is exactly 0<=E<=I, by self-duality of the PSD cone and the same trace pairing. Thus the full effect domain is retained. SectionROGFrame.whole_pure_carrier, applied to the whole Hermitian subspace and its PSD rank-one decomposition, identifies every extreme point of the entire trace-one base with rankOne(v) for a unit complex vector v. In particular v=(1,0,0) gives the actual original pure anchor p=diag(1,0,0).")),
                Paragraph(Text("HermitianExclusionKernel.exclusion_iff_kernel identifies the entire original D(rankOne(v)) with all PSD trace-one X satisfying Xv=0, including every mixed state and the original existential quantification over all proper real-linear effects. For PSD X, its zero-quadratic-form criterion and SectionROGFrame.pair_rankOne identify this kernel condition with inner(rankOne(v),X)=0. Consequently the normalized complement sigma(v)=(I-rankOne(v))/2 belongs to the same entire exclusion.")),
                Paragraph(Text("This complement also proves injectivity on every original pure label. If the full exclusions of rankOne(v) and rankOne(w) coincide, sigma(v) lies in both. Its zero pairing with rankOne(w), together with both unit-vector trace identities, gives inner(rankOne(w),rankOne(v))=1. SectionROGFrame.pairing_one_unique then forces the two pure matrices to be equal. No selected subset of pure labels is used.")),
                Paragraph(Text("The actual common effect at p is e(X)=inner(p,X), equal to Re(X(0,0)) on all of V. It confirms p and vanishes on the entire D(p). For any original common real-linear f, write f(X)=inner(E,X) by Riesz. Properness gives 0<=E<=I, confirmation gives inner(E,p)=1, and f(sigma(v))=0 gives trace(E)=1. The same frozen pairing_one_unique theorem forces E=p. Hence every common f equals this e: both common(C,u,p,e) and the original unique-existence predicate Regular(C,u,p) hold on their full domains.")),
                Paragraph(Text("For each original pure q, HermitianExclusionBall.all_pure_charts supplies an actual ExclusionChart of its entire exclusion with dimension exactly three. Substituting that dimension into the existing chart fields gives FullBall3Chart(C,u,q), proving EB3 on the entire original pure carrier. Choose any one of these actual charts at p as a. Applying regular_anchor_contact_criterion to the proved closedness, strict unit, generation, EB3, full exclusion injectivity, actual common e and Regular p yields one NativeChart(C,u,p,e,a) satisfying this document's complete ContactCriterion. Thus all hypotheses and the endpoint conclusion have one common native realization; no original-domain bridge is assumed.")),
                Paragraph(Text("This is an application of existing frozen kernel, full-chart and rank-one results to the conditional contact theorem. It establishes satisfiability of the complete original hypotheses. It supplies no example with delta>1, no classification of all admissible cones, no claim about a separate full regular-pure family or triangle condition, and no physical realization or literature priority claim.")),
                Paragraph(Text("This is Theorem 122.13, equation Q122.34. V is the original finite dimensional real normed space. C is the original closed generating convex cone, and u is strictly positive on every nonzero point of C. Strict positivity implies salience: x and -x cannot both be nonzero cone elements, since u(-x)=-u(x). No salience follows merely from the name PointedCone.")),
                Paragraph(Text("The entire original normalized base is K={x in C:u(x)=1}; P consists of all its extreme points. The effect interval E contains every original real-linear f with 0<=f<=u on all C. F_p={f in E:f(p)=1}, T_p(x)=min over F_p of f(x), and D_p={x in K:T_p(x)=0}. The existing comparison-attainment theorem identifies this set with the full exclusion, including its mixed states. A_p consists of all common effects e in F_p that vanish on all D_p. Regular(C,u,p) means A_p is a singleton. The supplied e is its member and therefore is exactly e_p.")),
                Paragraph(Text("EB3 asserts that every original pure label has a chart of its entire exclusion by the closed three-ball. Exclusion injectivity means D_p=D_q implies p=q for all original pure p,q. For the fixed anchor the supplied chart a has an injective affine map with a(closedBall(0,1))=D_p. In source notation c=a(0) and B=a.linear, so D_p=c+B closedBall(0,1). Its linear directions lie in ker(u). There is no assumption that the pure-state set is closed, and no pair, global leastness, matrix representation or dimension reduction premise.")),
                Paragraph(Text("Apply RegularAnchorContactCriterion.regular_anchor_native to precisely these hypotheses, p,e and a. It derives the restriction isomorphism on the real span of N_p={h>=0 on C:h(p)=0}, the actual linear H with H(a(w))=w, H(p)=0 and each coordinate in span(N_p), and g=u-e. It proves g>0 on all K except p, g(a(w))=1 for every coordinate w, and a finite positive M with norm(H(x))<=M*g(x) on the whole cone. Thus the normal interface, its support bounds and its actual three-dimensional coordinates are conclusions.")),
                Paragraph(Text("Define Z={H(x)/g(x):x in K except p}, S=closure(Z), rho(v)=sup over Z of -inner(v,z), and delta=min over the entire unit sphere of rho. The same original state supplies both H(x) and g(x). actual_image_bound and ball_subset_actual give boundedness and the entire unit ball in Z. The proved perspective construction gives convexity of Z. The shell is consequently compact and convex with nonempty ambient interior, and its support in direction -v is exactly rho(v).")),
                Paragraph(Text("The definitions width(a), minimum(n), shell(n) and boundaryDistance(n) are the original W(D_p), delta, S and set distance, respectively. Width takes the supremum of the entire original effect interval; width_attained proves that this is a maximum and supplies an actual effect and two antipodal chart states. The directional supremum is finite and Lipschitz. minimum_attained proves that its sphere infimum is a minimum and that delta>=1. boundaryDistance is the real infimum of dist(x,y) over the whole closed unit ball and the whole shell frontier; both sets are nonempty. The formula below uses smul for scalar multiplication of the whole set, intersection for set intersection and subset for set inclusion.")),
        Paragraph(Text("Keep the original finite dimensional real carrier V, closed generating cone C, strictly positive unit u, complete base K and full effect interval 0 <= f <= u. Every original exclusion has a full three-ball chart, and equality of exclusions identifies their pure labels. At the original regular anchor p the actual common confirmer e is unique. The NativeChart input is derived by RegularAnchorContactCriterion.regular_anchor_native from precisely these original hypotheses; it supplies neither a free positivity bridge nor a chosen subfamily of effects.")),
        Describe.Lean(DescribeId.Create("actual-image"), DeclarationHandle.Create(Owner + "actualImage"),
            H("Entire actual ratio image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Z is the image of every x in K other than p under H(x)/g(x), where g=u-e. NativeChart proves g is positive on this entire domain. No closedness of the pure state carrier is assumed."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("convex-image"), DeclarationHandle.Create(Owner + "actual_image_convex"),
            H("Convexity of the entire actual image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For two original states x,y and nonnegative weights s,t summing to one, normalize s*x/g(x)+t*y/g(y) by d=s/g(x)+t/g(y). Both gaps are strictly positive, hence d is positive. The resulting original base state has gap 1/d and its actual ratio is the requested convex combination. It cannot be the anchor. Closure preserves convexity; the existing whole-image norm bound makes S compact. The entire actual unit ball lies in S, giving nonempty ambient interior."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("rho"), DeclarationHandle.Create(Owner + "rho"),
            H("Actual directional support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("rho(v) is the supremum of -inner(v,z) over the whole actual ratio image. It is the exact source supremum of -inner(v,H(x))/g(x) over all x in K other than p."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actual-bound"), DeclarationHandle.Create(Owner + "actual_image_bound"),
            H("Whole actual image is bounded"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There is a finite positive M bounding the norm of every actual ratio image. Divide the proved whole-cone NativeChart bound by the strictly positive gap on K except p."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("inner-ball"), DeclarationHandle.Create(Owner + "ball_subset_actual"),
            H("The whole inner ball is actual"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every vector w in the closed unit ball is the ratio image of the actual state a(w), with gap exactly one. This state cannot equal p, whose gap is zero."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("support-bounded"), DeclarationHandle.Create(Owner + "rho_values_bdd"),
            H("Every full support supremum is bounded"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every vector v the entire set of support readings on Z is bounded above by norm(v)*M. The real supremum therefore has its ordinary upper-bound meaning."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("rho-upper"), DeclarationHandle.Create(Owner + "rho_le_iff"),
            H("Whole-base support bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real r and every coordinate vector v, rho(v)<=r is equivalent to -inner(v,H(x))<=r*g(x) for every original base state x other than p. The whole-cone NativeChart bound proves that the defining supremum is finite."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("rho-lower"), DeclarationHandle.Create(Owner + "rho_unit_lower"),
            H("Actual inner-ball lower bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every unit v, rho(v)>=1 because the actual original chart point a(-v) has g=1 and H=-v. This uses an actual state in the original exclusion."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("direction"), DeclarationHandle.Create(Owner + "direction"),
            H("Original directional linear effect"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The real linear functional direction(v) on V is inner(v,H). Its coordinate expansion lies in the entire signed normal span. The proved restriction isomorphism, rather than an additional premise, reconstructs every normalized positive annihilator with slope v as g+direction(v)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("antipodal"), DeclarationHandle.Create(Owner + "rho_one_iff_antipodal"),
            H("Exact actual antipodal criterion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every unit v, rho(v)=1 exactly when some effect in the entire original interval takes one at a(v) and zero at a(-v). Positivity is derived on the full original cone from the ratio bound; ExclusionWidthCompactness.comparison_zero_iff identifies actual comparison zero with exclusion in both directions, so an arbitrary original separating effect enters the existing comparison and slope-body theorem. The source direction v and the actual chart antipodes are retained without reversing or replacing their carriers."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("oscillation"), DeclarationHandle.Create(Owner + "oscillation"),
            H("Entire exclusion oscillation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Oscillation is the supremum of f on the entire original exclusion minus its infimum there. This is ExclusionWidthCompactness.oscillation on the same entire exclusion. Every original real linear effect is continuous in the finite dimensional topology."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("width"), DeclarationHandle.Create(Owner + "width"),
            H("Full original effect width"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("W(D(p)) is the ExclusionWidthCompactness.width of the entire exclusion: the supremum of its oscillation over all effects in the full original interval 0<=f<=u. The attainment theorem proves this is the source maximum, so the supremum notation does not weaken the source definition or remove an effect."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("width-attained"), DeclarationHandle.Create(Owner + "width_attained"),
            H("Actual full-effect width attainment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There exist a real linear effect f on the original carrier and a unit coordinate vector v such that W(D(p))=f(a(v))-f(a(-v)). The same actual f maximizes at a(v) and minimizes at a(-v) over the whole exclusion. ExclusionWidthCompactness.width_attained supplies a maximizing effect and actual extrema on the compact entire exclusion. For that same effect, the affine slope formula supplies one unit direction with antipodal extrema, including the constant-slope case."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("width-one"), DeclarationHandle.Create(Owner + "width_one_iff_rho_one"),
            H("Exact width and actual unit-support equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Width equals one if and only if an actual unit direction v satisfies rho(v)=1. If width is one, its attaining effect has actual readings one and zero at its antipodal extrema. Conversely any effect supplied by the unit-support criterion gives a full-exclusion oscillation of at least one, while ExclusionWidthCompactness.original_exclusion_width bounds the whole width by one. The reverse inequality applies ExclusionWidthCompactness.effect_difference_le_width to the same actual separating effect and chart antipodes. All quantifiers range over the original cone, base, effect interval and actual full chart."))), DescribeRole.Theorem),
        Paragraph(Text("Keep the same finite dimensional real carrier V, original cone C, unit u, entire base K, pure anchor p, actual common effect e and full three-ball chart a. NativeChart is the derived interface of RegularAnchorContactCriterion.regular_anchor_native, obtained from the original closedness, strict positivity, generation, EB3, exclusion injectivity and regularity hypotheses. Every result below applies to that very interface. The ratio image and rho are defined on this same original domain; neither is replaced by a model or a restricted state family.")),
        Describe.Lean(DescribeId.Create("shell"), DeclarationHandle.Create(Owner + "shell"),
            H("Closed actual shell"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("S is the closure of the image of every state x in K other than p under H(x)/g(x), with g=u-e. The actual image need not be closed."))), DescribeRole.Definition),
        Paragraph(Text("actual_image_convex proves convexity of the entire actual ratio image by reweighting two original base states. Its closure is convex; the proved whole-image bound makes S compact, and the actual closed unit ball lies in S.")),
        Describe.Lean(DescribeId.Create("support"), DeclarationHandle.Create(Owner + "shell_support_le_iff"),
            H("Exact shell support relation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real bound r and every vector v, all z in S satisfy -inner(v,z)<=r exactly when rho(v)<=r. Continuous linear evaluation extends the upper bound from the entire actual image to its closure. Thus the ordinary support of S at -v is precisely the original rho(v)."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lipschitz"), DeclarationHandle.Create(Owner + "rho_lipschitz"),
            H("Global directional Lipschitz bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A finite positive M bounds every ratio vector. Cauchy-Schwarz bounds each change of support reading by M times norm(v-w). Taking the bounded real supremum in both directions gives the absolute difference estimate for all vectors v,w, and therefore continuity on the whole coordinate space."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("minimum"), DeclarationHandle.Create(Owner + "minimum"),
            H("Entire sphere minimum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The real infimum is taken over rho evaluated on the entire unit sphere of the actual three-dimensional coordinate space."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("attainment"), DeclarationHandle.Create(Owner + "minimum_attained"),
            H("Attainment and inner-ball lower bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Continuity on the nonempty compact sphere supplies an actual unit minimizing direction. Its value equals the defined infimum and is at least one; every other unit direction has value at least this same minimum. The infimum is therefore the source minimum, with no assumed attainment field."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("contact-direction"), DeclarationHandle.Create(Owner + "ball_frontier_direction"),
            H("Actual contact point identifies the direction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If z lies both in the closed inner ball and on the boundary of S, then norm(z)=1 and rho(-z)=1. A supporting functional exists because S is convex with nonempty interior. Riesz representation and normalization give its unit normal b. Inner-ball containment yields 1<=inner(b,z)<=norm(z)<=1; equality forces b=z. The direction in rho is exactly -z."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("unit-support-contact"), DeclarationHandle.Create(Owner + "rho_one_frontier"),
            H("Unit support gives the actual point -v"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For unit v with rho(v)=1, the actual image already contains -v, supplied by the original chart state a(-v). This point belongs to S and saturates its supporting inequality. Any interior neighborhood would contain a slightly farther point in direction -v, contradicting that inequality. Hence -v belongs to the shell boundary."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("minimum-contact"), DeclarationHandle.Create(Owner + "minimum_one_iff_contact"),
            H("Exact sphere-minimum and ball-boundary equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The minimum equals one exactly when the closed original coordinate unit ball meets the boundary of its actual shell. An attaining unit direction supplies the contact point -v. Conversely an actual contact z supplies the unit direction -z with rho(-z)=1, while the minimum is at least one. No smoothness, strict convexity or closedness of the actual ratio image is assumed."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("halfspaces"), DeclarationHandle.Create(Owner + "mem_shell_iff"),
            H("All unit support halfspaces reconstruct the actual shell"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A vector z belongs to S exactly when -inner(v,z)<=rho(v) for every unit v. For a point outside the actual closed convex S, strict separation supplies a real continuous functional. Its nonzero Riesz vector gives a unit direction contradicting the asserted inequality. This reconstruction is proved for the actual shell rather than supplied as a bridge premise."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("minimum-ball"), DeclarationHandle.Create(Owner + "minimum_ball_subset"),
            H("Containment at the minimum support radius"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The entire closed ball of radius delta=minimum(rho) lies in S. For every unit support direction, Cauchy-Schwarz bounds the reading of a vector in this ball by delta, which is no greater than its actual directional support. The proved halfspace reconstruction gives containment. Since delta>=1, this closed ball is exactly delta times the closed unit ball."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("strict-margin"), DeclarationHandle.Create(Owner + "strict_margin"),
            H("Strict containment and every boundary distance"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If delta>1, the entire original closed unit ball lies in the ambient interior of S. Every boundary point has norm at least delta, since the open ball of radius delta lies in the shell interior. The triangle inequality then gives dist(x,y)>=delta-1 for every inner-ball x and every boundary y."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("boundary-distance"), DeclarationHandle.Create(Owner + "boundaryDistance"),
            H("Distance of the whole ball from the whole boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The set distance is the real infimum of all distances dist(x,y), with x in the entire closed unit ball and y on the entire boundary of S. Both sets are nonempty: S contains the unit ball and is a bounded proper convex body, so its boundary is nonempty."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("positive-distance"), DeclarationHandle.Create(Owner + "strict_boundary_distance"),
            H("Positive distance from the actual boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For delta>1, the set distance is at least delta-1, and delta-1 is strictly positive. Nonemptiness of the distance-value set gives the ordinary real-infimum lower bound; the estimate covers every pair of actual points in the specified sets."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("contact-criterion"),DeclarationHandle.Create(Owner+"ContactCriterion"),
                    H("All contact and strict-scale clauses"),StatementSource.FromAuthor(Disp(
                        definition)),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("Here n is the derived normal chart for the same C,u,p,e,a. The displayed conjunction means width one if and only if minimum one, minimum one if and only if the closed unit ball meets the boundary of its actual shell, and the complete strict-delta conclusion. By transitivity it includes both directions between every pair of the three contact conditions. All boundaries and interiors are ambient in the actual coordinate space EuclideanSpace(R,Fin(3))."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-contact"),DeclarationHandle.Create(Owner+"regular_anchor_contact_criterion"),
                    H("Complete criterion on the original telescope"),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("The notation exclusionInjective(C,u) in the display means injectivity of p -> exclusion(C,u,p) on the entire original pure carrier. NativeChart in the existential conclusion is derived from the original hypotheses; no normal chart, H, support representation, continuity or attained minimum is supplied as an additional premise.")),
                        Paragraph(Text("For width one, width_attained gives a full original effect with oscillation one at a unit direction's antipodal states. The original effect bounds make its endpoint readings exactly one and zero. rho_one_iff_antipodal, using the original comparison and positive normal-body interfaces, gives rho(v)=1. Conversely rho(v)=1 supplies a full original separating effect, hence width one. This is width_one_iff_rho_one on the entire original effect domain. Since the attained sphere minimum is at least one, existence of a unit direction with rho(v)=1 is equivalent to delta=1, in both directions.")),
                        Paragraph(Text("If rho(v)=1 for a unit v, the actual point -v belongs to Z and saturates -inner(v,z)<=1 on S. A neighborhood in S would contain a point farther in direction -v and violate that inequality, so -v is on the boundary. Conversely a contact z in closedBall(0,1) and frontier(S) has a supporting nonzero functional. Its normalized Riesz vector b satisfies 1<=inner(b,z)<=norm(z)<=1. Equality gives norm(z)=1 and b=z, and therefore rho(-z)=1. These are the exact signs of rho_one_frontier and ball_frontier_direction. minimum_one_iff_contact supplies the second displayed equivalence.")),
                        Paragraph(Text("For delta>1, the proved separation theorem mem_shell_iff reconstructs the actual closed convex S from all its unit support halfspaces. Cauchy-Schwarz and delta<=rho(v) put every vector of norm at most delta in S, by minimum_ball_subset. Because delta is positive, the standard smul_unitClosedBall identity identifies this closed ball with delta times the entire closed unit ball. strict_margin puts the original unit ball in interior(S). Every frontier point has norm at least delta; the triangle inequality gives dist(x,y)>=delta-1 for every original inner-ball x and every frontier y. strict_boundary_distance takes the nonempty distance-value infimum and proves boundaryDistance>=delta-1>0.")),
                        Paragraph(Text("This is a conditional mathematical statement on the declared original cone and effect system. It neither assumes smoothness, strict convexity or closedness of Z nor derives contact from those properties. It makes no physical realization or literature novelty claim."))),DescribeRole.Theorem)
            )));
    }
}

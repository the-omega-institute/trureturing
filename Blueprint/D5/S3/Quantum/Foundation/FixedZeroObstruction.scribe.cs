using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FixedZeroObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/FixedZeroObstruction.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Dual => C("LinearMap", R, V("V"), R);
    private static Formula K => C("base", V("C"), V("u"));
    private static Formula P => C("pure", V("C"), V("u"));
    private static Formula Dp(Formula p) => C("exclusion", V("C"), V("u"), p);
    private static Formula A(Formula p) => C("fullZeroConfirmers", V("C"), V("u"), p);
    private static Formula Z(Formula p) => C("zeroEffects", V("C"), V("u"), p);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", V("V")), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, V("V")), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, V("V")), CloseBracket, Sp,
        All("C", C("PointedCone", R, V("V")), All("u", Dual, body))));
    private static Formula Premises(Formula body) => Context(Imp(C("IsClosed", V("C")),
        Imp(C("StrictPositiveUnit", V("C"), V("u")),
        Imp(Eq(C("span", R, V("C")), C("top")),
        Imp(C("exclusionBalls", V("C"), V("u")), body)))));
    private static DocumentBlock Decl(string name, string title, Formula f, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static DocumentBlock Def(string name, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    public DocumentDefinition Create()
    {
        Formula s = V("s"), t = V("t"), h = V("h"), g = V("g"), v = V("v"), x = V("x");
        Formula inj = C("InjectiveExclusionLabels", V("C"), V("u"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Entire original zero effects attain their global maximum in the exclusion face; whole-ball collapse obstructs every fixed complete zero test on one common edge.",
            H("Fixed zero effects on the entire original state body"), Blocks(
                Def("zeroEffects", "For every original pure t, this is exactly the set of original linear g satisfying proper(C,u,g) and g(t)=0."),
                Def("fullZeroConfirmers", "For every original pure s, this is exactly the set of original linear h satisfying confirms(C,u,s,h) and h(x)=0 for every x in the entire exclusion(C,u,s)."),
                Def("stateReadout", "For every original linear f, this is its continuous restriction to the entire subtype base(C,u), evaluated at every original normalized state."),
                Def("stateNorm", "For the original closed-cone and strictly-positive-unit hypotheses and every original linear f, this is the continuous-map supremum norm of stateReadout(f). The compact-space instance is obtained from compactness of the original base."),
                Def("faceMaximum", "For every original pure t and original linear h, this is sSup of the image of the entire exclusion(C,u,t) under h."),
                Def("zeroDistance", "Under original compact-base hypotheses, for every pure t and original linear h, this is Metric.infDist from stateReadout(h) to the image of the entire zeroEffects(C,u,t) under stateReadout."),
                Def("stableZeroWitness", "For every original s,r with r in exclusion(C,u,s), there exists one h in fullZeroConfirmers(C,u,s) such that for every pure sequence t(n) tending to r there exists a sequence g(n) of original linear effects, each in zeroEffects(C,u,t(n)), with stateNorm(g(n)-h) tending to zero. The h quantifier precedes the t sequence."),
                Def("openEdges", "For every original p,s with s in exclusion(C,u,p), and every original pure sequence t(n) tending to p, there exists an original pure sequence v(n), in exclusion(C,u,t(n)) at every index, tending to s."),
                Paragraph(Text("V is any finite dimensional real normed carrier, C is its closed generating cone, and u is strictly positive on every nonzero cone vector. K is the entire normalized base, P all its extreme points, and effects are the entire original interval between zero and u. StrictPositiveUnit denotes exactly that cone condition; InjectiveExclusionLabels denotes injectivity of p mapped to the whole exclusion. Every exclusion is an affine Euclidean closed ball of positive dimension, with dimensions allowed to vary.")),
                Paragraph(Text("zeroEffects(C,u,t) contains exactly the proper linear effects zero at t. fullZeroConfirmers(C,u,s) contains exactly the proper confirmers of s vanishing on all of its exclusion. stateReadout restricts a linear functional to every point of K as a continuous real function. stateNorm is the existing supremum norm of that function, so its value is the maximum absolute readout over all K. faceMaximum is the supremum on the entire exclusion; compactness makes it an attained maximum. zeroDistance is the existing metric infimum distance in C(K,R) to the image of the entire zero-effect fiber, preserving the original full-state norm.")),
                Paragraph(Text("The exclusion interface agrees with the original lower-envelope zero set: x belongs to exclusion(C,u,p) exactly when x is in K and comparison(C,u,p,x)=0. ContinuousFrameSum.effects_compact gives compactness of the entire original effect interval under strict positivity and generation. The confirming slice is closed and contains u, so every evaluation attains its minimum there; nonnegativity proves the stated equivalence. The pure global maximizer below therefore gives max over all K of g equal to max over the entire original D(t) of g, including g=0.")),
                Decl("zero_effect_maximizer", "A pure global maximizer in the entire exclusion", Premises(
                    All("t", P, All("g", Dual, Imp(In(g, Z(t)), Ex("v", P,
                        And(In(v, Dp(t)), All("x", V("V"), Imp(In(x, K), Seq(App(g,x), Le, Sp, App(g,v)))))))))),
                    "For a nonzero zero effect, its global maximum is strictly positive because the original pure states span V. Its compact exposed maximum face contains an original pure point. Normalizing by this actual maximum gives a proper confirmer; complementing it puts the same point in the full exclusion of t. For the zero effect, any extreme point of the nonempty compact exclusion is also extreme in K. Thus all indices, including zero effects, admit such a choice."),
                Decl("full_zero_faces", "The exact zero and one faces", Premises(Imp(inj,
                    All("s", P, All("h", Dual, Imp(In(h, A(s)), And(
                        Eq(C("ZeroFace", K, h), Dp(s)), Eq(C("OneFace", K, h), new Formula.SetLiteral([s])))))))),
                    "ZeroFace(K,h) is the set of x in K with h(x)=0; OneFace uses h(x)=1. Any pure one-point v has an exclusion containing the whole exclusion of s. The ball-face theorem and faithful labels force v=s. The one-face is compact, exposed and convex. Krein-Milman makes it the closed convex hull of its extreme points, all of which are the same s. Mixed limit states are therefore included without assuming P closed or finite pure decomposition."),
                Decl("fixed_zero_distance_bound", "The entire-state repair lower bound", Premises(
                    All("s", P, All("t", P, All("h", Dual, Imp(In(h, A(s)),
                        Seq(C("divide", C("subtract", D(1), C("faceMaximum", t, h)), D(2)), Le, Sp,
                            C("zeroDistance", V("C"), V("u"), t, h))))))),
                    "For any actual g zero at t choose its pure global maximizer v in the full exclusion. Evaluation at s and v is bounded by the continuous-map supremum norm. The resulting inequality is 1 <= max over D(t) of h plus twice the distance between g and h. Taking the infimum over the entire zero-effect image gives the displayed bound. No faithful-label condition is needed for this estimate."),
                Decl("stable_zero_implies_open_edges", "One fixed witness per edge implies all-index lifting", Premises(Imp(inj,
                    Imp(C("stableZeroWitness", V("C"), V("u")), C("openEdges", V("C"), V("u"))))),
                    "stableZeroWitness quantifies every original s,r with r in D(s), then chooses one h in fullZeroConfirmers(s), then quantifies every sequence of original pure t(n) tending to r, and finally chooses proper g(n) zero at each t(n), with stateNorm(g(n)-h) tending to zero. openEdges quantifies every original p,s with s in D(p), every pure t(n) tending to p, and returns pure v(n) in D(t(n)) for every index with v(n) tending to s. Original zero symmetry first reverses the input edge. The repair bound forces the maxima of h on D(t(n)) to tend to one. Pure maximizers exist on every compact exposed face, including every initial index. Compactness of K and the singleton one-face force the full sequence to converge to s. No pure-point closedness, ball continuity, continuous selector, rate, Hilbert representation, or selected effect menu is assumed."),
                Describe.Lean(DescribeId.Create("exclusion-limit-labels"), DeclarationHandle.Create(Owner + "exclusion_limit_labels"), H("Whole-limit labels without closed pure points"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite dimensional real normed V, original closed generating pointed cone C and strictly positive unit u, assume every entire original exclusion has an injective affine closed Euclidean ball chart of positive dimension, with dimensions allowed to vary. For every sequence pn of actual pure points, every x in V with pn(n) tending to x, and every nonempty compact G with hausdorffDist(D(pn(n)),G) tending to zero, the following conjunction holds. If the map from all original pure p to its entire D(p) is injective, then (i) G containing two distinct points forces x to be an actual pure point, and (ii) for every q in V, G={q} and x not pure force q to be actual pure and x to belong to intrinsicInterior(real,D(q)). Independently of that injectivity assumption, if x is actual pure then the entire G is contained in D(x). Membership of x and all of G in the original K is derived, and closedness of the pure locus is never assumed.")),
                    Paragraph(Text("Choose an original full zero confirmer for every whole D(pn(n)). Compactness of the entire effect interval gives one convergent effect subsequence. Every point of the same whole compact limit is recovered by nearest points along those indices, so one actual limit effect e satisfies e(x)=1 and vanishes on all G. The existing common_zero_pure declaration in ExclusionWidthCompactness is used directly: two distinct common zeros force the confirmed state pure. For singleton G and mixed x, the compact exposed one-face of e contains an actual pure p distinct from x. The complementary effect u-e confirms q and has the two distinct zeros x,p, so the same original declaration forces q pure. It also places x in the entire D(q). The original chart_boundary identity and intrinsic frontier transport identify the whole relative boundary with the actual pure points of D(q); mixed x therefore lies in its intrinsic interior. The proof uses the closed convex hull and extreme points directly, without an extra finite pure decomposition or an inner product on V."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("fixed-zero-distance-obstruction"), DeclarationHandle.Create(Owner + "fixed_zero_distance_obstruction"), H("One common edge obstructs every fixed zero test"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite dimensional real normed V with the same original closed cone, strict unit and generating hypotheses, assume that every actual pure p has an injective affine chart of the entire D(p) by the closed Euclidean three-ball, and that p mapped to D(p) is injective. For every original pure sequence pn, every x,q in V with pn(n) tending to x and hausdorffDist(D(pn(n)),{q}) tending to zero, there exist actual pure s and r with r in D(s), and one sequence tn of actual pure points tending to r, such that for every fixed original linear h in fullZeroConfirmers(C,u,s), h(tn(n)) tends to zero and the real filter liminf atTop of zeroDistance(hc,hs,tn(n),h) is strictly positive. The existential choices of the edge and entire tn sequence precede the universal h. Only the positive lower bound may depend on h. The norm and zero-effect fiber are exactly the original whole-state objects defined above. Membership of x in K follows from compactness of K; no assumption of O, WZ, closed P, ball continuity, continuous axes, Pair, or an inner product on V is added.")),
                    Paragraph(Text("When x is pure, the original pure_pair_in_ball declaration supplies two distinct actual pure points of D(x). Choose s different from q, set r=x and tn=pn, and use original zero symmetry. The full_zero_faces theorem makes s the unique one-point of every fixed complete zero confirmer, including among mixed states. The limit set {q} lies in K and avoids s; compact maxima converge to h(q)<1. This branch never assumes q pure.")),
                    Paragraph(Text("When x is mixed, exclusion_limit_labels proves q pure and x in intrinsicInterior(real,D(q)). Choose actual pure tn in D(pn(n)) at every index. Whole-fiber convergence forces tn to q, and original zero symmetry puts pn(n) in D(tn(n)). Native compactness of all nonempty compact subsets of the original K supplies one common strictly increasing index subsequence and one whole compact limit G of these exchanged exclusions. Nearest-point recovery preserves convex combinations, so G is convex; moving-point closure gives x in G, and the pure-label upper graph gives G contained in D(q). This argument imposes no lower bound on a limiting rank or diameter, so point, segment, disk and full-dimensional limits all remain allowed. If G were the whole D(q), the already proved ExclusionIncidence.affine_ball_boundary_limit applies directly to the arbitrary injective three-ball charts of the actual exchanged fibers and D(q). The points pn on their original pure boundaries would force x into the boundary of D(q), contradicting its intrinsic-interior location. Full-rank boundary transport is used only in that equality case. Thus G is a proper subset. Since D(q) is the closed convex hull of its actual pure extreme points, at least one actual pure s of D(q) lies outside the same closed convex G. Set r=q and retain that one exchanged subsequence before considering any h.")),
                    Paragraph(Text("For either branch, compactness attains max_G h at an original state. The singleton one-face and s outside G give max_G h<1 for every fixed h. Vietoris upper neighborhoods and nearest-point recovery prove that maxima over the entire moving exclusions converge to max_G h. The existing fixed_zero_distance_bound then bounds the actual zeroDistance from below eventually by (1-max_G h)/4>0. Distance to the actual zero effect supplies a finite upper bound, making the positive real liminf conclusion valid. Continuity gives h(tn(n)) tending to h(r)=0. All subsequences, G, s,r and tn are fixed before h; no test-dependent subsequence is introduced."))), DescribeRole.Theorem),
                Paragraph(Text("The mathematical conclusions are conditional on the original geometric hypotheses. They assert no physical realization, reconstruction theorem, global novelty, or empirical claim. The source-bound Reg mirrors retain faithful telescope bridges and actual-positive laws; lawful four-slot registrations remain unfinished.")))));
    }
}

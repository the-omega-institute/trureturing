using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalWidthContactDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalWidthContact.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] xs) => xs.Length == 1 ? xs[0] : new Formula.Logic(xs[0], FormulaLogicOperator.And, And(xs[1..]));
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula Sub(Formula x, Formula y) => C("sub", x, y);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula K => C("base", V("C"), V("u"));
    private static Formula P => C("pure", V("C"), V("u"));
    private static Formula Dp(Formula p) => C("exclusion", V("C"), V("u"), p);
    private static Formula Proper(Formula f) => C("proper", V("C"), V("u"), f);
    private static Formula WB(Formula face, Formula m) => C("WidthBound", V("C"), V("u"), face, m);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));
    private static Formula BasicContext(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));

    public DocumentDefinition Create()
    {
        Formula p = V("p"), q = V("q"), r = V("r"), m = V("M"), b = V("b"), e = V("e");
        Formula xy = V("xy"), zw = V("zw"), x = C("fst", xy), y = C("snd", xy);
        Formula z = C("fst", zw), w = C("snd", zw);
        Formula Contact(Formula a, Formula c) => And(In(a, K), In(c, K),
            Eq(App(b, a), D(1)), Eq(App(b, c), D(0)),
            Eq(Sub(q, r), C("smul", m, Sub(a, c))));
        Formula strict = All("x", Space, Imp(In(V("x"), V("C")),
            Imp(Ne(V("x"), D(0)), Lt(D(0), App(V("u"), V("x"))))));
        Formula inj = All("p1", P, All("p2", P,
            Imp(Eq(Dp(V("p1")), Dp(V("p2"))), Eq(V("p1"), V("p2")))));
        Formula zero = All("z", Space, Imp(In(V("z"), Dp(p)), Eq(App(e, V("z")), D(0))));
        Formula readings = Imp(Lt(m, D(1)), All("e", Dual,
            Imp(C("confirms", V("C"), V("u"), p, e), Imp(zero,
                And(Lt(D(0), App(e, x)), Eq(App(e, x), App(e, y)), Lt(App(e, y), D(1)),
                    C("not", In(x, Dp(p))), C("not", In(y, Dp(p))))))));
        Formula conclusion = Ex("xy", C("Prod", Space, Space), And(Contact(x, y),
            All("zw", C("Prod", Space, Space), Imp(Contact(z, w), Eq(zw, xy))), readings));
        Formula full = Context(All("b", Dual, Imp(And(C("IsClosed", V("C")), strict,
            Eq(C("span", R, V("C")), C("top")), C("exclusionBalls", V("C"), V("u")), inj),
            All("p", P, All("M", R, Imp(Lt(D(0), m), Imp(WB(Dp(p), m), Imp(Proper(b),
                All("q", Space, All("r", Space, Imp(And(In(q, Dp(p)), In(r, Dp(p)),
                    Eq(Sub(App(b, q), App(b, r)), m)), conclusion)))))))))));
        Formula width = BasicContext(All("F", C("Set", Space), All("M", R,
            new Formula.Logic(WB(V("F"), m), FormulaLogicOperator.Iff,
                All("f", Dual, Imp(Proper(V("f")), All("x", Space, All("y", Space,
                    Imp(And(In(V("x"), V("F")), In(V("y"), V("F"))),
                        Le(Sub(App(V("f"), V("x")), App(V("f"), V("y"))), m))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every positive attained width on a whole original exclusion face determines one unique actual joint contact pair, with strict equal readings for all confirming effects when the width is below one.",
            H("The unique joint contact pair of an attained original width"), Blocks(
                Paragraph(Text("V is an arbitrary finite dimensional real normed space. C is the original closed generating pointed convex cone, u is strictly positive on its nonzero vectors, K is the entire slice C intersect {u=1}, and P comprises every extreme point of K. Every effect is an original real-linear functional satisfying 0<=f<=u on the whole cone. Every entire exclusion D(p) is an injective affine image of a nondegenerate finite Euclidean closed ball, and equality of two such original exclusions forces equality of their pure labels. The result includes the original three-dimensional ball case. No inner product on V, closedness or compactness of P, pair-face hypothesis, unique confirmation premise or retraction is required.")),
                H("Application: adjacent complete confirmation and the original normalized perturbation"),
                Paragraph(Text("Keep this same entire K, cone, unit, full effect interval and injective exclusion-ball family. Fix arbitrary original pure labels p,q with q in F=D(p), and arbitrary complete confirmers a of q and e of p: a and e are proper, a(q)=e(p)=1, a vanishes on all of D(q), and e vanishes on all of F. Suppose M<1 and WidthBound(C,u,D(q),M). In the original global-width notation, W(D(r)) is the maximum oscillation over every proper original effect and M=sup_r W(D(r)); then e(x)-e(y)<=osc_D(q)(e)<=W(D(q))<=M for all x,y in D(q). This supplies precisely the local WidthBound premise, without restricting the effect domain or replacing the global supremum by a different quantity. The argument below applies to every such p,q,a,e.")),
                Paragraph(Text("Use top_subsingleton_of_zero_exclusion with the label q and effect a. Since a(q)=1, its whole one-value face is {q}. If y is any zero of a in K, the definition of exclusion puts y in D(q). Exclusion symmetry (FacetZeroGluing.exclusion_symmetric) gives p in D(q), so the width bound for the same original e gives 1-e(y)<=M and hence e(y)>=1-M>0. Also e(q)=0. Thus for every x,y in K with a(x)=1 and a(y)=0, e(x)<e(y). Only this inclusion of the zero face in D(q) is needed; no extra equality of faces is assumed.")),
                Paragraph(Text("There is an elementary compact-extrema route to the required perturbation. On the compact nonempty set T={(x,y) in K times K : e(y)<=e(x)}, let d=max_T(a(x)-a(y)). Compactness follows from base_compact, the compact-product and closed-intersection rules, and continuity of the two original effects; IsCompact.exists_isMaxOn supplies an actual maximizing pair. The diagonal makes T nonempty. The effect bounds give d<=1. Equality would force a(x)=1 and a(y)=0 at that pair, contradicting the preceding strict contact inequality. Hence d<1. Put t=(1-d)/2>0 and g=a+t e. If e(y)<=e(x), then g(x)-g(y)<=d+t=(1+d)/2<1. Otherwise t(e(x)-e(y))<0 and a(x)-a(y)<=1, again giving g(x)-g(y)<1. These are applications of compact extrema and real inequalities, with no differentiation of a moving family.")),
                Paragraph(Text("Take the actual minimum lo and maximum hi of this same g on the entire K, using IsCompact.exists_isMinOn and IsCompact.exists_isMaxOn, and set s=hi-lo. Their ordered pair gives s<1. The original exclusion_ball_faces result makes F a nondegenerate compact ball. Choose r in F distinct from q. Whole-face rigidity gives a(r)<a(q)=1, while e is zero on all of F, so g(q)-g(r)=1-a(r)>0 and therefore s>0. Define the original real-linear functional b=(g-lo u)/s. Its bounds 0<=b<=1 on K imply 0<=b<=u on the whole original cone by positive-unit rescaling, exactly as in the existing normalized_effect proof and CircuitBalancedConfirmation.cone_bound. Thus b belongs to the original full effect interval, with no change of unit or restriction of state space.")),
                Paragraph(Text("On the entire F, g=a because e vanishes there. Its normalization therefore gives osc_F(b)=osc_F(a)/s. Compactness supplies the actual extrema on F, and the same q,r show osc_F(a)>0. Since 0<s<1, osc_F(b)>osc_F(a)>0. This derives the original adjacent-complete-confirmation conclusion and the specified formula b=(a+t e-(min_K(a+t e))u)/(max_K(a+t e)-min_K(a+t e)). The minimum, maximum and positive parameter all refer to one common original realization. The compact-extrema results used here are in pinned Mathlib (Mathlib.Topology.Order.Compact); the full-cone and whole-face premises come from the existing project results. This exposition records their application and introduces no separate mathematical declaration.")),
                Paragraph(Text("This route establishes the finite positive-parameter conclusion within the stated convex model. It does not establish the distinct one-sided expansions max_X(b+t h)=max_X(b)+t max_argmax(b)(h)+o(t) and min_X(b+t h)=min_X(b)+t min_argmin(b)(h)+o(t) for arbitrary continuous b,h on an arbitrary nonempty compact X. In particular the perturbation argument alone supplies neither derivative statement. No model realizing the strict-width hypotheses, physical instrument implementation or literature priority is asserted.")),
                Describe.Lean(DescribeId.Create("top-exposed"), DeclarationHandle.Create(Owner + "top_exposed"), H("The whole original one-value face is exposed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The one-value set of any original proper effect is an exposed face of the entire original base. The density label-limit proof uses this original-site result to derive purity of a cluster point after showing that this whole face is a singleton."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("top-subsingleton"), DeclarationHandle.Create(Owner + "top_subsingleton_of_zero_exclusion"), H("Whole one-value-face rigidity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With the original closed generating cone, strictly positive unit, full positive-dimensional exclusion balls and injective original exclusion map, any proper original effect vanishing on the entire D(p) has a subsingleton whole one-value face. Its actual pure maximizers all have the same full exclusion as p; injectivity and compact convex generation then control every state in that face. The label-limit proof starts its limit state in K and uses this whole-face result, without assuming that the state is pure."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("width-bound"), DeclarationHandle.Create(Owner + "WidthBound"),
                    H("The full effect width bound"), StatementSource.FromAuthor(Disp(width)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("WidthBound(C,u,F,M) quantifies every original effect and every ordered pair of points of the entire F. Together with b(q)-b(r)=M for one proper b and q,r in F, it says exactly that M is the attained maximum ordered contrast. Thus it expresses W(F)=M without choosing a smaller effect or state domain."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-width-contact"), DeclarationHandle.Create(Owner + "original_width_contact"),
                    H("One actual pair, uniqueness and all strict confirming readings"),
                    StatementSource.FromAuthor(Disp(full)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Fix the original p, F=D(p), M>0, an effect b and points q,r in F attaining the full width M. The conclusion selects one ordered pair (x,y) of original states. It has b(x)=1, b(y)=0 and q-r=M(x-y). Every other ordered pair with these same properties equals it. If M<1, this same pair satisfies 0<e(x)=e(y)<1 for every original confirmer e of p which vanishes on all of F. Both points are then outside F. No claim says that both contacts are pure or that different maximizing b have the same contacts.")),
                        Paragraph(Text("For an arbitrary continuous linear functional h, compactness supplies its actual minimum a and maximum z on K. If its oscillation s=h(z)-h(a) is positive, the full-cone effect (h-h(a)u)/s has contrast at most M on q,r. Hence h((q-r)/M)<=s. If s=0, h(q)=h(r), giving the same inequality. The closed convex set K-K is the intersection of its containing half-spaces, so the same vector (q-r)/M lies in K-K. This gives one actual pair x,y in K. Its b contrast equals one, and the original effect bounds force b(x)=1 and b(y)=0. In particular the resulting member of X-Y satisfies every directional support inequality for X-Y; no directional optimizers are combined.")),
                        Paragraph(Text("For any original full-amplitude effect, its two contact sets are compact convex faces. If the zero face is not a pure singleton, the original proper-face classification makes it an entire D(t). For every pure s in the one face, the same effect puts D(t) inside D(s). Whole-ball facial rigidity and injectivity of the exclusion labels force s=t. Krein-Milman then makes the entire one face a singleton. Thus at least one contact face is a singleton, and the fixed difference uniquely determines the other endpoint.")),
                        Paragraph(Text("Every confirmer e vanishing on F annihilates q-r, so both contacts have equal readings. A common zero reading would put both contacts in F, where the original b would have contrast one, contradicting its full width M<1. A common reading one puts both contacts in the singleton one face of e, contradicting their b readings one and zero. This proves the strict bounds for all such e after the single pair has been fixed.")),
                        Paragraph(Text("For the global maximum-width application, take the whole F supplied by the positive attained global maximum in the original width theorem 118.15 and use the same attained b and its actual two extrema. No new global maximum theorem is asserted here. The local conclusion applies to every positive attained whole-face width and requires no restriction of p to uniquely confirmed labels. It does not produce a common exclusion ball containing the two contacts, does not force M=1 and does not establish the global width-one or dense-triangle condition. This is a deduction in the specified full-effect convex model, with no claim of literature priority or physical instrument realization."))), DescribeRole.Theorem))));
    }
}

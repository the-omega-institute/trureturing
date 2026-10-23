using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedSplitReferenceConvergenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedSplitReferenceConvergence.";
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Side(Formula a) => Call("inter", Call("side", Call("true")), Call("preimage", V("projection"), a));
    private static Formula Moving(Formula a, Formula n) => Call("mu", Call("inter", a, Call("U", n)));
    private static Formula Weak(Formula s) => Call("toWeakDual", Call("signedFunctional", s));
    private static Formula TV(Formula s) => Call("totalVariationRealUniv", s);
    private static Formula ProjectedLimit() => Call("Tendsto",
        Seq(V("n"), Sp, Mapsto, Sp,
            Call("apply", Call("map", Call("s", V("n")), V("projection")), V("A"))),
        Call("atTop"), Call("nhds", Call("mu", V("A"))));
    private static Formula SideBound() => Call("Eventually", Call("atTop"),
        Seq(V("n"), Sp, Mapsto, Sp,
            Call("abs", Seq(Call("apply", Call("s", V("n")), Side(V("A"))),
                Sp, Minus, Sp, Moving(V("A"), V("n")))),
            Sp, Le, Sp, Call("epsilon", V("n"))));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("K", Call("Type", V("u"))), Call("CompactMetricTotallyDisconnectedBorel", V("K"))),
        Seq(All("Y", Call("Set", V("K"))), All("Z", Call("Set", V("K"))),
            Call("IsClosed", V("Y")), Sp, Land, Sp, Call("IsClosed", V("Z")), Sp, Rightarrow),
        Seq(V("L"), Sp, Eq, Sp, Grp(Seq(V("p"), Colon, Call("Product", V("K"), Call("Bool")), Sp,
            V("suchThat"), Sp, Grp(Seq(Call("mem", Call("fst", V("p")), V("Y")), Sp, Land, Sp,
                Call("snd", V("p")), Sp, Eq, Sp, Call("false"))), Sp, Lor, Sp,
            Grp(Seq(Call("mem", Call("fst", V("p")), V("Z")), Sp, Land, Sp,
                Call("snd", V("p")), Sp, Eq, Sp, Call("true")))))),
        Seq(All("C", Call("Real")), All("s", Fn(Call("Nat"), Call("SignedMeasure", V("L"))))),
        Seq(Call("Nonneg", V("C")), Sp, Land, Sp, Grp(Seq(All("n", Call("Nat")),
            TV(Call("s", V("n"))), Sp, Le, Sp, V("C"))), Sp, Rightarrow),
        Seq(All("mu", Call("SignedMeasure", V("K"))), All("U", Fn(Call("Nat"), Call("Set", V("K"))))),
        Seq(Grp(Seq(All("n", Call("Nat")), Call("MeasurableSet", Call("U", V("n"))))), Sp, Land, Sp,
            Call("Monotone", V("U")), Sp, Rightarrow),
        Seq(All("epsilon", Fn(Call("Nat"), Call("Real"))),
            Call("Tendsto", V("epsilon"), Call("atTop"), Call("nhds", Num(0))), Sp, Rightarrow),
        Seq(Grp(Seq(All("A", Call("Set", V("K"))),
            Call("IsClopen", V("A")), Sp, Rightarrow, Sp, ProjectedLimit())), Sp, Rightarrow),
        Seq(Grp(Seq(All("A", Call("Set", V("K"))),
            Call("IsClopen", V("A")), Sp, Rightarrow, Sp, SideBound())), Sp, Rightarrow),
        Seq(Exists, Sp, V("nu"), Colon, Call("SignedMeasure", V("L")), Comma, Sp,
            TV(V("nu")), Sp, Le, Sp, V("C"), Sp, Land, Sp,
            Call("Regular", Call("jordanPosPart", V("nu"))), Sp, Land, Sp,
            Call("Regular", Call("jordanNegPart", V("nu"))), Sp, Land, Sp,
            Call("Tendsto", Seq(V("n"), Sp, Mapsto, Sp, Weak(Call("s", V("n")))),
                Call("atTop"), Call("nhds", Weak(V("nu")))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed signed reference and increasing-set side errors give actual represented whole-sequence convergence on a closed Boolean split.",
        H("Signed reference convergence on the actual closed split"),
        Blocks(
            Paragraph(Text(
                "K is any compact metric totally disconnected Borel space. Y and Z are closed; neither coverage nor nonemptiness is assumed. "
                + "Split is exactly the subtype of K × Bool consisting of (Y,false) and (Z,true), with first-coordinate projection π and clopen sheets S_false and S_true.")),
            Describe.Lean(
                DescribeId.Create("exists-signed-limit-of-reference"),
                DeclarationHandle.Create(Owner + "exists_signed_limit_of_reference"),
                H("Represented signed split limit"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The sequence s consists of arbitrary actual SignedMeasure values on Split with totalVariation.real(univ) ≤ C and C ≥ 0. "
                        + "One fixed signed μ on K is used for every test and every stage. The measurable U_n increase, and ε_n tends to zero. "
                        + "For each fixed ambient clopen A, projected s_n(A) tends to μ(A), and eventually the absolute true-sheet error against μ(A ∩ U_n) is at most ε_n. No global nonnegativity of ε is required.")),
                    Paragraph(Text(
                        "For a clopen W of Split, the projected images of W ∩ S_e and Wᶜ ∩ S_e are disjoint compact closed sets. "
                        + "Projection is injective within each fixed tag. The existing compact zero-dimensional clopen separator supplies an ambient clopen B_e with W ∩ S_e = S_e ∩ π⁻¹(B_e); it does not assert that the projected traces themselves are ambient clopens.")),
                    Paragraph(Text(
                        "Signed continuity from below gives μ(A ∩ U_n) → μ(A ∩ ⋃ U_n). The vanishing absolute-error bound gives this same limit for s_n(S_true ∩ π⁻¹(A)). "
                        + "Disjoint finite additivity proves s_n(W) = (π_*s_n)(B_false) − s_n(S_true ∩ π⁻¹(B_false)) + s_n(S_true ∩ π⁻¹(B_true)). "
                        + "Thus every clopen coordinate converges, hence is Cauchy. The live ClopenCauchyConvergence helper then yields an actual signed ν, the same variation upper bound, regular Jordan parts, and weak-star convergence of the entire represented sequence.")),
                    Paragraph(Text(
                        "Empty K and Split, C = 0, negative coefficients, and mixed signs are included. The conclusion is a variation bound, not variation-mass convergence or exact norm preservation. "
                        + "This bridge is an internal reference-convergence step for F in exists_signed_split_successor. It does not supply the CH construction, every-choice convergence, an anti-homeomorphism, either remaining analytic endpoint, or a complete solution of Talagrand Problem 8.2. FullCHLeanSolved = 0 and officialSolved = 0."))),
                DescribeRole.Theorem))));
}

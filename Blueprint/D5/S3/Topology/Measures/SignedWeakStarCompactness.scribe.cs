using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedWeakStarCompactnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedWeakStarCompactness.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Fn(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Signed(Formula K) => Call("SignedMeasure", K);
    private static Formula TV(Formula s) => Call("totalVariationRealUniv", s);
    private static Formula At(Formula f, string n) => Call("apply", f, V(n));
    private static Formula Weak(Formula s) =>
        Call("toWeakDual", Call("signedFunctional", s));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("K", Seq(V("Type"), Underscore, Grp(V("u")))),
            Inst("MetricSpace", V("K")), Inst("CompactSpace", V("K")),
            Inst("MeasurableSpace", V("K")), Inst("BorelSpace", V("K"))),
        Seq(All("C", Call("Real")),
            All("s", Fn(Call("Nat"), Signed(V("K"))))),
        Seq(Call("Nonneg", V("C")), Sp, Rightarrow, Sp,
            Grp(Seq(All("n", Call("Nat")), TV(At(V("s"), "n")), Sp,
                Le, Sp, V("C"))), Sp, Rightarrow),
        Seq(Exists, Sp, V("phi"), Colon, Fn(Call("Nat"), Call("Nat")), Comma, Sp,
            Exists, Sp, V("mu"), Colon, Signed(V("K")), Comma, Sp,
            Call("StrictMono", V("phi")), Sp, Land, Sp,
            TV(V("mu")), Sp, Le, Sp, V("C"), Sp, Land, Sp,
            Call("Tendsto",
                Seq(V("n"), Sp, Mapsto, Sp,
                    Weak(Call("apply", V("s"), At(V("phi"), "n")))), Call("atTop"),
                Call("nhds", Weak(V("mu")))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact metric signed-measure sequences have represented weak-star subsequences with the same total-variation bound.",
        H("Represented weak-star subsequence compactness for signed measures"),
        Blocks(
            Paragraph(Text(
                "K is an arbitrary compact metric space with its Borel measurable structure. "
                + "For every real C with 0 ≤ C and every sequence s of actual finite SignedMeasure K whose real total variation on univ is at most C, "
                + "the theorem produces a strictly monotone subsequence and an actual SignedMeasure K limit with the same bound.")),
            Describe.Lean(
                DescribeId.Create("exists-subsequence-tendsto-signed-functional"),
                DeclarationHandle.Create(Owner + "exists_subsequence_tendsto_signedFunctional"),
                H("Actual signed-measure weak-star subsequence supplier"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the displayed statement, apply(f,x) means f(x). The first Tendsto argument is the pointwise sequence n ↦ toWeakDual(signedFunctional(s(phi(n)))), indexed by n : Nat. "
                        + "The source filter is atTop on Nat and the limit filter is nhds(toWeakDual(signedFunctional(mu))). totalVariationRealUniv(t) means t.totalVariation.real univ.")),
                    Paragraph(Text(
                        "The proof writes each signed measure as the difference of its actual Jordan positive and negative finite measures. "
                        + "The pairs with summed mass at most C form a closed subset of the product of two compact finite-measure mass balls, using the pinned Prokhorov compactness theorem and continuity of mass.")),
                    Paragraph(Text(
                        "The pair-to-functional map is continuous because evaluation at each continuous real test function is the difference of the two continuous finite-measure integrals. "
                        + "Its compact image in the weak dual is metrizable because C(K,Real) is separable for compact metric K. "
                        + "Sequential compactness of the image therefore supplies a strictly monotone subsequence and a point still represented by a finite-measure pair.")),
                    Paragraph(Text(
                        "The represented limit is the difference of that pair. Vector-measure variation_sub_le and the Jordan mass identity give total variation at most the original C, including C=0 and signed measures of either sign. "
                        + "No Nonempty K, positivity, probability normalization, finite support, or zero-dimensional hypothesis is used; empty K remains covered.")),
                    Paragraph(Text(
                        "This supplier only provides the reference represented weak-star limit for compact metric successor stages. "
                        + "It does not construct norm-preserving lifts, settle the CH scheduler or recursion, extend to the nonmetrizable final layer, or solve Problem 8.2."))),
                DescribeRole.Theorem))));
}

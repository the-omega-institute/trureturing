using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class L1UniformIntegrableWeakDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Inst(string n, Formula t) =>
        Seq(OpenBracket, Call(n, t), CloseBracket, Sp);
    private static Formula L => Call("RealLone", V("mu"));
    private static Formula At(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("Omega", Seq(V("Type"), Underscore, Grp(V("u")))),
            Inst("MeasurableSpace", V("Omega")), All("mu", Call("Measure", V("Omega"))),
            Inst("IsFiniteMeasure", V("mu"))),
        Seq(All("f", Fn(Call("Nat"), L)),
            Call("UniformIntegrable", Call("representatives", V("f")), D(1), V("mu")),
            Sp, Rightarrow),
        Seq(Exists, Sp, V("j"), Colon, Fn(Call("Nat"), Call("Nat")), Comma, Sp,
            Exists, Sp, V("v"), Colon, L, Comma, Sp,
            Call("StrictMono", V("j")), Sp, Land, Sp,
            All("phi", Call("ContinuousRealLinearFunctional", L)),
            Call("Tendsto", Seq(V("n"), Sp, Mapsto, Sp,
                At(V("phi"), At(V("f"), At(V("j"), V("n"))))),
                Call("atTop"), Call("nhds", At(V("phi"), V("v")))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform integrability gives a genuinely weakly convergent real L1 subsequence over any finite measure.",
        H("Weak sequential compactness from uniform integrability"),
        Blocks(
            Paragraph(Text("RealLone(mu) denotes MeasureTheory.Lp Real 1 mu, and representatives(f) denotes its actual coerced representative sequence. "
                + "The sigma algebra is arbitrary and the finite measure may be zero. No nonatomicity, countable generation, positivity or ambient separability is assumed.")),
            Describe.Lean(DescribeId.Create("uniform-integrability-weak-subsequence"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/L1UniformIntegrableWeak.exists_weak_subsequence"),
                H("A weak subsequence for every uniformly integrable real L1 sequence"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib UniformIntegrable.spec supplies uniform hard-tail bounds at errors 1/(m+1). "
                    + "Restriction to the strict complementary level set gives bounded L2 functions. "
                    + "The inclusion L2 → L1 preserves the identical almost-everywhere class and is bounded by the finite-measure exponent comparison, including zero total measure. "
                    + "The common Hilbert approximation theorem therefore gives one increasing selector and an actual L1 limit, tested against every continuous real linear functional. "
                    + "This proves the weak-extraction part of the classical subsequence-splitting argument. "
                    + "It supplies neither the disjoint-carrier selection nor the signed-measure transfer or the full CH/Talagrand conclusion."))), DescribeRole.Theorem))));
}

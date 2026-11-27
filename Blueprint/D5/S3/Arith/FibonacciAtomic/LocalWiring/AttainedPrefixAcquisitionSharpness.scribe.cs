using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class AttainedPrefixAcquisitionSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/AttainedPrefixAcquisitionSharpness.";
    private static Formula Barrier => Seq(
        D(2), Leq, Sp, F.Id("n"), Lt, Sp, F.Id("N"), Quad, Sp,
        new Formula.Subscript(F.Id("v"), F.Id("n")), Lt, Sp, F.Id("m"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fixed hard source per promise defeats every earlier mature stopping cut.",
        H("Sharp worst mature update deadline"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-single-adaptive-hard-source"),
            DeclarationHandle.Create(Prefix + "single_adaptive_hard_source"),
            H("Exact task separation before the attainable deadline"),
            StatementSource.FromAuthor(Disp(Barrier)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each valid positive target promise a single actual lawful " +
                    "source works across all earlier mature cuts. It is a fixed " +
                    "periodic pulse for the bounded binary class, a fixed cycle for " +
                    "the bounded Moore class, or a fixed seed for the entire public " +
                    "row. At every earlier mature cut there is a lawful alternative " +
                    "with the same mature prefix but different labels, a different " +
                    "literal next-cut presence answer, and different future behavior.")),
                Paragraph(Text(
                    "The alternative is chosen per cut, not per random tape. Under " +
                    "one common proper tape law, intersect the finitely many relevant " +
                    "alternative success events and the hard-source success event. " +
                    "At the realized early cut, the full accessible record coincides " +
                    "on the paired runs, including the stop and observed replies. " +
                    "The distinct correct tasks make early zero-error stopping " +
                    "impossible for each task separately; no bound on local or " +
                    "service step counts was imposed.")),
                Paragraph(Text(
                    "Together with the attained program, this proves the sharp " +
                    "class-uniform worst update deadline for mature readiness. It " +
                    "does not minimize paid reads, address costs or total work, " +
                    "and it does not say every source is difficult."))),
            DescribeRole.Theorem))));
}

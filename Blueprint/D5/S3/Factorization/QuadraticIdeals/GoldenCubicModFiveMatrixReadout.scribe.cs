using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicModFiveMatrixReadoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite F5 matrix powers and normalized traces give uniformly calibrated Frobenius readouts.",
        H("Exact finite matrix certificates modulo five"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-mod-five-projective-order-five"),
                DeclarationHandle.Create(Module + "projective_five_of_noncentral_repeated_root"),
                H("The noncentral repeated-root class has exact projective order five"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For determinant one and trace squared four, a nonscalar matrix first becomes scalar at "
                    + "the fifth positive power. The finite certificate uses the same powers as matrix "
                    + "multiplication."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod-five-nonsquare-trace-fibers"),
                DeclarationHandle.Create(Module + "nonsquare_fibers_normalized_trace"),
                H("Both nonsquare determinant fibers have the same normalized trace law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant-three trace is multiplied by two. The five normalized trace counts, in "
                    + "order zero through four, are 20, 20, 30, 30 and 20 in each nonsquare determinant fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod-five-nonsquare-exact-projective-orders"),
                DeclarationHandle.Create(Module + "exact_nonsquare_projective_length"),
                H("Three trace conditions read the exact projective order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonsquare determinant the least positive scalar power is two for zero trace, four "
                    + "when the trace squared is twice the determinant, and six otherwise. The finite check "
                    + "excludes every smaller positive scalar power."))),
                DescribeRole.Theorem))));
}

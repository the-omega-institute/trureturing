using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringIndStep2EstimatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mean-value bound for a nonzero shift",
        H("Mean-value bound for a nonzero shift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("indstep2estimates"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringIndStep2Estimates.integral_norm_T_pow_le_R"),
                H("Mean-value bound for a nonzero shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("For polynomials of degree d ≥ 3 and bounded coefficients, a mean-value estimate at degree d−1 bounds the unit-interval norm integral of every nonzero shift in the prescribed box."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadsum"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringIndStep2Estimates.integral_sum_pow_four"),
                H("Fourth moment of the displacement sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("Integration over the unit interval retains the four phase fibers whose integer phases sum to zero, weighted by the product of their cardinalities."))),
                DescribeRole.Theorem)
        )));
}

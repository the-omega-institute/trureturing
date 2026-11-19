using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class ThreePunctureResidueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/ThreePunctureResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residue Balance at Zero, One, and Infinity.",
        H("Residue Balance at Zero, One, and Infinity"),
        Blocks(
            Describe.Lean(DescribeId.Create("residue-sum"),
                DeclarationHandle.Create(Prefix + "residue_sum"),
                H("Residue balance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtract the finite principal parts at zero and one and extend over both punctures. "
                    + "The inverse-coordinate bound at infinity gives a bounded entire remainder. "
                    + "Liouville and the first inverse coefficient then give the residue balance."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("a-chart-residue-invariant"),
                DeclarationHandle.Create(Prefix + "aChart_residue_invariant"),
                H("Residue in the iterate coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The substitution u ↦ −u/(1+u) includes its derivative. "
                    + "Each pole of order at least two contributes only higher poles. "
                    + "A simple pole contributes its original coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("residue-sum-of-differential-expansions"),
                DeclarationHandle.Create(Prefix + "residue_sum_of_differential_expansions"),
                H("Residue balance for three local differentials"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The expansions at zero and one use local translated coordinates. "
                    + "The expansion at infinity is for the differential pulled back by inversion, including the derivative of inversion. "
                    + "The three coefficients of the simple poles sum to zero."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CMJet;

internal sealed class CMJetCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CMJet/Correction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The restricted derivative gives an all-order recurrence for the concrete section jets.",
        H("The restricted derivative recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("correction-second"),
                DeclarationHandle.Create(Prefix + "correction_second"),
                H("The correction has zero second derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordinary and restricted derivations commute on S. Cancelling S gives the "
                        + "derivative of the correction, whose next derivative vanishes by the base scalar law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-jet-recurrence"),
                DeclarationHandle.Create(Prefix + "integer_jet_recurrence"),
                H("Recurrence for the integer section jets reduced at an odd prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reflection forces the correction to vanish at the origin. The product rule then "
                        + "retains only the first derivative of the correction. The two scalar "
                        + "coefficients are given by iterates on the original curve."))),
                DescribeRole.Theorem)
        )));
}

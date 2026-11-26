using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CMJet;

internal sealed class CMJetActualRestrictedRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CMJet/ActualRestrictedRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two polynomial variables carry the logarithmic derivative and the section factor.",
        H("The polynomial extension and integer lemniscatic section jets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("extended-iter-s-multiple"),
                DeclarationHandle.Create(Prefix + "extendedIter_s_multiple"),
                H("The quotient by S at every order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product rule updates the quotient inside the coefficient ring by adding hZ times the previous quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("jet-zero-order"),
                DeclarationHandle.Create(Prefix + "jet_zero_order"),
                H("The zeroth section jet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluation gives one in the zeroth column and zero in every positive column."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("iterated-leibniz"),
                DeclarationHandle.Create(Prefix + "iterated_leibniz"),
                H("The all-order product rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Differentiation and Pascal’s identity give the binomial convolution of the two lists of derivatives."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("restricted-base"),
                DeclarationHandle.Create(Prefix + "restricted_base"),
                H("Restriction to the curve"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The iterate preserves the embedded base and agrees there with the original prime operator."))),
                DescribeRole.Theorem)
        )));
}

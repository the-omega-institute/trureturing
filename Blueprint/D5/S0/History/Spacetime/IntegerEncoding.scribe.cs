using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class IntegerEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tagged natural magnitudes give an exact finite set representation of signed integers.",
        H("Integer HF Codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerEncoding.int_code_equiv"),
                H("All signed integers have exactly the legal codes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The structural grammar permits tag zero with any natural magnitude and tag one with "
                    + "a strictly positive magnitude. Natural codes use von Neumann ordinals. Negative zero "
                    + "is excluded, and case analysis on Int proves both round trips."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-code-reconstruction"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/IntegerEncoding.encode_decodeInt"),
                H("Reconstruction preserves the literal code"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every structurally legal code is recovered after decoding. This finite representation "
                    + "supplies the coordinate and time fields of archive records."))),
                DescribeRole.Theorem))));
}

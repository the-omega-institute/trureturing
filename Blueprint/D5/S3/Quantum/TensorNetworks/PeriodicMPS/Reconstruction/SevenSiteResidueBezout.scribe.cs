using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueBezoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBezout";
    private const string Title = "Bézout identity for the seven-site quotient tables";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensiteresiduebezout-linequotient-degree"),
                DeclarationHandle.Create(Module + ".lineQuotient_degree"),
                H("Degree of the two tabulated quotients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each of the deleted rows zero and one, the tabulated line quotient over the field modulo 1009 has natural degree forty-six. Its coefficient at degree forty-six is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensiteresiduebezout-concrete-bezout"),
                DeclarationHandle.Create(Module + ".concrete_bezout"),
                H("Polynomial identity over the residue field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplying the two table quotients by their corresponding tabulated multipliers and adding gives the constant polynomial one modulo 1009. The coefficient convolution verifies the identity at each possible nonzero degree."))),
                DescribeRole.Theorem))));
}

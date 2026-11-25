using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueComparisonDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueComparison";
    private const string Title = "Interpolation of the literal seven-site cofactor quotients";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensiteresiduecomparison-identify-line-quotient"),
                DeclarationHandle.Create(Module + ".identify_line_quotient"),
                H("Identification of the affine quotient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For deletion of row zero or one modulo 1009, take an exact quotient of the literal cofactor by the mixed-trace coordinate. Assume the stated value and derivative comparisons at the seven entry sample points and the tabulated determinant identities at the forty-seven quotient nodes. Then the quotient restricted to the specified affine line equals the tabulated polynomial. The mixed-trace coordinate is nonzero at each quotient node, so cancellation and the degree bound permit interpolation."))),
                DescribeRole.Theorem))));
}

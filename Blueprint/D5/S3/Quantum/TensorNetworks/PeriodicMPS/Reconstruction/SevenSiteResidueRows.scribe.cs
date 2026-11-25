using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueRowsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueRows";
    private const string Title = "Interpolation of the seven-site critical matrices on the residue line";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensiteresiduerows-evaluatedrows-eq"),
                DeclarationHandle.Create(Module + ".evaluatedRows_eq"),
                H("Exact critical matrix on the affine line"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume that every Pauli observation entry and each listed first partial agrees with its table at the seven sample points modulo 1009. At any parameter of the specified affine line, evaluation of the corresponding polynomial critical matrix equals the matrix assembled from the tables, for every row deletion. The individual value and derivative polynomials are identified by their degree bounds."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueBatch18Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch18";
    private const string Title = "Seven-site cofactor values at line nodes 18 through 23";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Cofactor("0", "18", "18"),
            Cofactor("1", "18", "18"),
            Cofactor("0", "19", "19"),
            Cofactor("1", "19", "19"),
            Cofactor("0", "20", "20"),
            Cofactor("1", "20", "20"),
            Cofactor("0", "21", "21"),
            Cofactor("1", "21", "21"),
            Cofactor("0", "22", "22"),
            Cofactor("1", "22", "22"),
            Cofactor("0", "23", "23"),
            Cofactor("1", "23", "23"))));

    private static DocumentBlock Cofactor(string row, string node, string residue) =>
        Describe.Lean(DescribeId.Create("sevensiteresiduebatch18-row-" + row + "-node-" + node),
            DeclarationHandle.Create(Module + ".cofactor_at_" + row + "_" + node),
            H("Cofactor deleting row " + row + " at residue " + residue), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Over the field modulo 1009, at line parameter " + residue + " the determinant of the evaluated rows after deleting row " + row + " equals the mixed-trace coordinate times the corresponding quotient-table evaluation. A unit lower triangular factor and an upper triangular factor verify this determinant value."))),
            DescribeRole.Theorem);
}

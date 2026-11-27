using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueBatch0Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch0";
    private const string Title = "Seven-site cofactor values at line nodes 0 through 5";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Cofactor("0", "0", "0"),
            Cofactor("1", "0", "0"),
            Cofactor("0", "1", "1"),
            Cofactor("1", "1", "1"),
            Cofactor("0", "2", "2"),
            Cofactor("1", "2", "2"),
            Cofactor("0", "3", "3"),
            Cofactor("1", "3", "3"),
            Cofactor("0", "4", "4"),
            Cofactor("1", "4", "4"),
            Cofactor("0", "5", "5"),
            Cofactor("1", "5", "5"))));

    private static DocumentBlock Cofactor(string row, string node, string residue) =>
        Describe.Lean(DescribeId.Create("sevensiteresiduebatch0-row-" + row + "-node-" + node),
            DeclarationHandle.Create(Module + ".cofactor_at_" + row + "_" + node),
            H("Cofactor deleting row " + row + " at residue " + residue), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Over the field modulo 1009, at line parameter " + residue + " the determinant of the evaluated rows after deleting row " + row + " equals the mixed-trace coordinate times the corresponding quotient-table evaluation. A unit lower triangular factor and an upper triangular factor verify this determinant value."))),
            DescribeRole.Theorem);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueBatch24Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch24";
    private const string Title = "Seven-site cofactor values at line nodes 24 through 29";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Cofactor("0", "24", "24"),
            Cofactor("1", "24", "24"),
            Cofactor("0", "25", "25"),
            Cofactor("1", "25", "25"),
            Cofactor("0", "26", "26"),
            Cofactor("1", "26", "26"),
            Cofactor("0", "27", "27"),
            Cofactor("1", "27", "27"),
            Cofactor("0", "28", "28"),
            Cofactor("1", "28", "28"),
            Cofactor("0", "29", "29"),
            Cofactor("1", "29", "29"))));

    private static DocumentBlock Cofactor(string row, string node, string residue) =>
        Describe.Lean(DescribeId.Create("sevensiteresiduebatch24-row-" + row + "-node-" + node),
            DeclarationHandle.Create(Module + ".cofactor_at_" + row + "_" + node),
            H("Cofactor deleting row " + row + " at residue " + residue), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Over the field modulo 1009, at line parameter " + residue + " the determinant of the evaluated rows after deleting row " + row + " equals the mixed-trace coordinate times the corresponding quotient-table evaluation. A unit lower triangular factor and an upper triangular factor verify this determinant value."))),
            DescribeRole.Theorem);
}

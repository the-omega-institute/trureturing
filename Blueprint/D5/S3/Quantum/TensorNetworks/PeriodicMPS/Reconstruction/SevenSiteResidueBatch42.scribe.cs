using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueBatch42Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch42";
    private const string Title = "Seven-site cofactor values at line nodes 42 through 46";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Cofactor("0", "42", "43"),
            Cofactor("1", "42", "43"),
            Cofactor("0", "43", "44"),
            Cofactor("1", "43", "44"),
            Cofactor("0", "44", "45"),
            Cofactor("1", "44", "45"),
            Cofactor("0", "45", "46"),
            Cofactor("1", "45", "46"),
            Cofactor("0", "46", "47"),
            Cofactor("1", "46", "47"))));

    private static DocumentBlock Cofactor(string row, string node, string residue) =>
        Describe.Lean(DescribeId.Create("sevensiteresiduebatch42-row-" + row + "-node-" + node),
            DeclarationHandle.Create(Module + ".cofactor_at_" + row + "_" + node),
            H("Cofactor deleting row " + row + " at residue " + residue), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Over the field modulo 1009, at line parameter " + residue + " the determinant of the evaluated rows after deleting row " + row + " equals the mixed-trace coordinate times the corresponding quotient-table evaluation. A unit lower triangular factor and an upper triangular factor verify this determinant value."))),
            DescribeRole.Theorem);
}

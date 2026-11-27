using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteResidueBatch12Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch12";
    private const string Title = "Seven-site cofactor values at line nodes 12 through 17";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Cofactor("0", "12", "12"),
            Cofactor("1", "12", "12"),
            Cofactor("0", "13", "13"),
            Cofactor("1", "13", "13"),
            Cofactor("0", "14", "14"),
            Cofactor("1", "14", "14"),
            Cofactor("0", "15", "15"),
            Cofactor("1", "15", "15"),
            Cofactor("0", "16", "16"),
            Cofactor("1", "16", "16"),
            Cofactor("0", "17", "17"),
            Cofactor("1", "17", "17"))));

    private static DocumentBlock Cofactor(string row, string node, string residue) =>
        Describe.Lean(DescribeId.Create("sevensiteresiduebatch12-row-" + row + "-node-" + node),
            DeclarationHandle.Create(Module + ".cofactor_at_" + row + "_" + node),
            H("Cofactor deleting row " + row + " at residue " + residue), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Over the field modulo 1009, at line parameter " + residue + " the determinant of the evaluated rows after deleting row " + row + " equals the mixed-trace coordinate times the corresponding quotient-table evaluation. A unit lower triangular factor and an upper triangular factor verify this determinant value."))),
            DescribeRole.Theorem);
}

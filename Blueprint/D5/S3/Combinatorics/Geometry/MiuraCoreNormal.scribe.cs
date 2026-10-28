using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreNormalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreNormal.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneously reduced residual cores.", H("Simultaneously reduced residual cores"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorenormal-0"),
                DeclarationHandle.Create(Prefix + "NoAdjacentFrozen"), H("No consecutive frozen pair remains"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The column axis contains no consecutive pair of columns satisfying their genuine frozen equations. Applying the same predicate after transposition tests the row axis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorenormal-1"),
                DeclarationHandle.Create(Prefix + "residual_reduced_joint_core_exists"), H("A finite reduced core on both axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive exact extremum split and every actual residual rectangle with dimensions at least two, there is an actual related residual core with both dimensions between 2 and 2(a+b)-1, with no adjacent frozen pair on either axis. Reduction terminates because the sum of the dimensions decreases at every deletion. The conclusion establishes a reduced core, without identifying different reduction choices or their expansion fibers."))), DescribeRole.Theorem))));
}

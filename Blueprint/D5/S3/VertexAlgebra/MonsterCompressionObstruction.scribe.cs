using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class MonsterCompressionObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/MonsterCompressionObstruction.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/basak2017monstercharactercarry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An additive compression of all ground sections erases every character direction and cannot preserve quadratic spin.",
        H("Ground-Section Compression Obstructs Spin Descent"),
        Blocks(
            Paragraph(Text("Let E be the three-dimensional binary vector space and let a finite "
                + "sign table satisfy the character-carry equations. Each ground section has a "
                + "defect coordinate and a character coordinate.")),
            Describe.Lean(
                DescribeId.Create("ground-section-compression-obstructs-spin"),
                DeclarationHandle.Create(Prefix + "compression_obstruction"),
                H("Character kernel and failure of spin descent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every target abelian group and additive map from the "
                    + "six-bit label group, requiring the images of all ground sections to add "
                    + "as coarse defects forces every pure character label into the kernel. "
                    + "Two labels then have the same image but different quadratic spin values, "
                    + "so the spin cannot factor through the map. The proof uses three independent "
                    + "determinant-carry directions and works for every permitted sign table. "
                    + "Basak's twisted-group-algebra calculation is historical background. "
                    + "This finite-label result assumes no VOA realization, physical fusion "
                    + "operation, or condensation procedure."))),
                DescribeRole.Theorem))));
}

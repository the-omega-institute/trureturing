using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class BlockMatricesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block Matrices", H("Block Matrices"),
        Blocks(
            Paragraph(Text("Two-block matrices: inclusion matrices, block embedding of GL_r, block-triangular criteria.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/BlockMatrices.rangeParabolic"),
                H("rangeParabolic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The parabolic subgroup of GL_n(R) of matrices whose rows with index in the image of u vanish in the columns with index outside that image.")))))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class BlockDiagonalDetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block Diagonal Det", H("Block Diagonal Det"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/BlockDiagonalDet.sq_le_norm_det_blockDiagPart"),
                H("sq_le_norm_det_blockDiagPart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("|det| of the block diagonal part of g in U(p,q) is at least (‖g‖/2)².")))))));
}

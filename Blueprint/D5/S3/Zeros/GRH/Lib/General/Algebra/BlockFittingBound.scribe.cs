using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class BlockFittingBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block Fitting Bound", H("Block Fitting Bound"),
        Blocks(
            Paragraph(Text("Fitting ideal bounded by a length over a DVR, through a matrix algebra quotient.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/BlockFittingBound.exists_rows_addVal_det_le"),
                H("exists_rows_addVal_det_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ψ: A → M_d(O) be onto, N ⊆ A^ι an A-submodule, p ≠ 0, b < v(p). If the w in ((O/p)^d)^ι killed by N through ψ lie in a submodule of length ≤ b, some square matrix B with rows in N has v(det ψ(B)) ≤ b.")))))));
}

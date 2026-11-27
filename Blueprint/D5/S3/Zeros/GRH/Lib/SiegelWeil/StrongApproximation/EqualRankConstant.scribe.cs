using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.StrongApproximation;

internal sealed class EqualRankConstantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal Rank Constant", H("Equal Rank Constant"),
        Blocks(
            Paragraph(Text("Automorphic function invariant at a split place, compact group and torus is constant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/StrongApproximation/EqualRankConstant.apply_eq_apply_one"),
                H("apply_eq_apply_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let D be continuous on [U(W)], W split along a line, right invariant under points supported on S ∪ S̄ (S nonempty) and integral points off S. If invariance under the radical makes D on the Levi independent of the torus, then D is constant.")))))));
}

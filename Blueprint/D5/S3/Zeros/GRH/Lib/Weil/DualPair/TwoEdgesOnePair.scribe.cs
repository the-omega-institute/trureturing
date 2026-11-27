using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class TwoEdgesOnePairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Edges One Pair", H("Two Edges One Pair"),
        Blocks(
            Paragraph(Text("Heisenberg group law and its normalisation by the dual pair, in rational coordinates. Parabolic elements act on the zero term along an isotropic subspace; determinant bookkeeping. Tensor of two Weil representations as one pair via adjoint; theta kernels multiply.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/TwoEdgesOnePair.liftWeilFin"),
                H("liftWeilFin"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The Weil representation of the finite adelic U(V) × U(V') ∋ (g, h) on the finite part 𝒲_f of Hom(V,V'), twisted by (aυ^⌊rk V/2⌋)(det h) (aυ^⌊rk V'/2⌋)(det g)⁻¹.")))))));
}

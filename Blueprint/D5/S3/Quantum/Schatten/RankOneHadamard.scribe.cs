using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class RankOneHadamardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank-one Schur multipliers and diagonal weights.", H("RankOneHadamard"), Blocks(
            Paragraph(Text("A complex square matrix of rank at most one factors as an outer product x yᵀ, including the zero matrix and dimension zero. Consequently W ⊙ G is diagonal(x) W diagonal(y).")),
            Paragraph(Text("Write each scalar as a unit-modulus phase times its nonnegative modulus, choosing phase one at zero. The resulting diagonal phase matrices are unitary, so every unitarily invariant norm removes both phases. There are common nonnegative weights aᵢ = |xᵢ| and bᵢ = |yᵢ| for every W: the first Schur factor has norm N(diagonal(a) W diagonal(b)), and its inverse-transpose counterpart has norm N(diagonal(a) (W⁻¹)ᴴ diagonal(b)). The latter identity uses transpose and adjoint invariance and the reality of the diagonal weights.")),
            Paragraph(Text("The factorization reuses Mathlib's one-dimensional range characterization. The phase-removal and inverse-adjoint bridge supply the algebraic reduction of the rank-one Zhang–Li assertion to nonnegative diagonal products; they do not by themselves prove the required lower bound for expanding matrices.")))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class UnitarilyInvariantNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitarily invariant norms and diagonal gauges.", H("UnitarilyInvariantNorm"), Blocks(
            Paragraph(Text("A unitarily invariant norm is a nonnegative definite norm on complex square matrices, absolutely homogeneous over complex scalars, subadditive, and invariant under multiplication on either side by a unitary matrix. Singular-value decomposition reduces its value to the real diagonal gauge of the singular values. Transposition and adjunction preserve the norm.")),
            Paragraph(Text("Convex combinations of a diagonal matrix and its one-coordinate sign reflection realize a coordinate contraction. Iterating gives monotonicity under coordinatewise absolute-value domination. Finite T-transforms and the existing majorization transfer theorem then imply monotonicity of the diagonal gauge under weak majorization of nonnegative vectors; only the vector being dominated must be decreasing.")),
            Paragraph(Text("Permutation conjugation preserves the real diagonal gauge. If Pσ has its nonzero entry in row i at column σ(i), then diagonal(a) Pσ diagonal(b) has norm equal to the diagonal gauge of the matched products aᵢ bσ(i). Multiplying on the right by Pσᴴ proves this identity. These results are standard consequences of unitary invariance and finite majorization and make no mathematical originality claim.")))));
}

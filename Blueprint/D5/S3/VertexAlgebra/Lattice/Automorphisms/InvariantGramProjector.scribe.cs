// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Automorphisms;

internal sealed class InvariantGramProjectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal projection onto an invariant real subspace commutes with each isometry and gives compatible real and complex matrix identities.",
        H("Invariant Gram Projectors"),
        Blocks(
            Paragraph(Text("Let B be a symmetric positive-definite bilinear form on a finite-dimensional real vector space V. Let W be a proper nonzero subspace. Each member g of the indexed family of linear equivalences preserves B and satisfies g(x) ∈ W if and only if x ∈ W.")),
            Describe.Lean(
                DescribeId.Create("invariant-gram-projector-map"),
                DeclarationHandle.Create(Prefix + "exists_invariant_projector"),
                H("Equivariant orthogonal projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is a linear endomorphism P with range W and P² = P, distinct from zero and the identity. It satisfies B(Px,y) = B(x,Py) for all x,y and commutes with each g. Positivity makes the restricted form on W nondegenerate, giving the decomposition into W and its orthogonal complement. The isometries preserve both summands, so projection commutes with them."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariant-gram-projector-real-matrix"),
                DeclarationHandle.Create(Prefix + "exists_invariant_projector_matrix"),
                H("Real matrix identities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any real basis with a finite index type and decidable equality, let G be the matrix of B and M(g) the matrix of the isometry g in that basis. There is a real matrix P with P² = P, P ≠ 0 and P ≠ 1. It satisfies PᵀG = GP and commutes with each M(g). The transpose equation is the matrix form of bilinear self-adjointness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariant-gram-projector-complex-matrix"),
                DeclarationHandle.Create(Prefix + "exists_invariant_projector_complex_matrix"),
                H("Complex matrix identities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Embed the entries of G and M(g) into ℂ. There is a complex matrix P with P² = P, P ≠ 0 and P ≠ 1, satisfying PᵀG = GP and commuting with every complexified M(g). The injective ring map preserves the real matrix equations and both inequalities. Self-adjointness here uses the bilinear transpose."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdEigenspacePairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complex P48q Gram form pairs the two primitive cubic eigenspaces perfectly and gives dual current bases indexed by Fin 16.",
        H("Complementary Cubic Eigenspaces of P48q"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eigenspaces-orthogonal"),
                DeclarationHandle.Create(Prefix + "eigenspace_pairing_eq_zero"),
                H("Orthogonality for eigenvalues whose product differs from one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let A be a complex-linear endomorphism preserving a complex bilinear form B. If x and y are in the eigenspaces for α and μ and αμ differs from one, then B(x,y) = 0. Invariance gives B(x,y) = αμ B(x,y), and the difference of the two scalar factors is invertible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-pairing"),
                DeclarationHandle.Create(Prefix + "movingPairing"),
                H("The restricted pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an endomorphism A, a bilinear form B and a complex scalar ζ, restrict the first argument of B to the ζ eigenspace and the second to the ζ² eigenspace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moving-pairing-perfect"),
                DeclarationHandle.Create(Prefix + "movingPairing_isPerfPair"),
                H("The primitive cubic eigenspaces pair perfectly"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the complex vector space is finite-dimensional, A³ is the identity, ζ is a primitive cube root, and B is nondegenerate and preserved by A. The restriction of B to the ζ and ζ² eigenspaces is perfect.")),
                    Paragraph(Text("The cyclic averages (x + α²Ax + αA²x)/3 for α equal to 1, ζ and ζ² lie in the corresponding eigenspaces and sum to x. A vector in either moving eigenspace that pairs to zero with the opposite space also pairs to zero with the fixed space and its own eigenspace by orthogonality. The decomposition then puts it in a radical of B, where it vanishes. Both restricted radicals therefore vanish, giving the dual equivalences in finite dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-action"),
                DeclarationHandle.Create(Prefix + "p48qAction"),
                H("The complex row action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The P48q endomorphism on complex functions on Fin 48 is the scalar extension of the catalogue row action x ↦ xM."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-form"),
                DeclarationHandle.Create(Prefix + "p48qForm"),
                H("The complex Gram form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The P48q bilinear form on complex functions on Fin 48 is the form with matrix G, the catalogue integer Gram matrix cast to the complex numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-form-invariant"),
                DeclarationHandle.Create(Prefix + "p48qForm_invariant"),
                H("The row action preserves the complex Gram form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("For any two complex rows x and y, the pairing of xM with yM equals the pairing of x with y. This follows by casting the integral identity MGMᵀ = G and evaluating the resulting bilinear forms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-form-nondegenerate"),
                DeclarationHandle.Create(Prefix + "p48qForm_nondegenerate"),
                H("The complex Gram form has zero radicals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The integral left inverse remains a left inverse over the complex numbers. Taking determinants gives a product equal to one, so the complex Gram matrix is nonsingular and the bilinear form is nondegenerate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-fixed-average"),
                DeclarationHandle.Create(Prefix + "p48qAverage_mem_fixed"),
                H("The cyclic average is fixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("For every complex row x and the P48q action A, the vector (x + Ax + A²x)/3 belongs to the kernel of A − 1. Applying A cycles the three summands because A³ is the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-moving-pairing"),
                DeclarationHandle.Create(Prefix + "p48q_movingPairing_isPerfPair"),
                H("The P48q moving pairing is perfect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("For every primitive complex cube root ζ, the P48q Gram form restricts to a perfect pairing of the ζ eigenspace with the ζ² eigenspace. The cube, isometry and inverse identities supply the hypotheses of the general pairing theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-moving-isotropic"),
                DeclarationHandle.Create(Prefix + "p48q_moving_isotropic"),
                H("Each P48q moving eigenspace is totally isotropic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("For every primitive complex cube root ζ, the Gram pairing of any two vectors from the ζ eigenspace is zero, and the same holds for two vectors from the ζ² eigenspace. The squared eigenvalues are respectively ζ² and ζ, both different from one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-moving-dimensions"),
                DeclarationHandle.Create(Prefix + "p48q_moving_finrank"),
                H("Both moving eigenspaces have dimension sixteen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("For every primitive complex cube root ζ, the ζ and ζ² eigenspaces each have complex dimension sixteen. The three distinct eigenspaces form a direct sum of total dimension forty-eight. The fixed-rank certificate gives sixteen fixed dimensions, and perfectness makes the two remaining dimensions equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-moving-basis"),
                DeclarationHandle.Create(Prefix + "p48qBasis"),
                H("Basis for the residue-one currents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each primitive complex cube root ζ, choose a basis indexed by Fin 16 of the ζ eigenspace, using its dimension."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-opposite-basis"),
                DeclarationHandle.Create(Prefix + "p48qOppositeBasis"),
                H("Dual basis for the residue-two currents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each primitive complex cube root ζ, transport the coordinate dual of the chosen ζ basis to the ζ² eigenspace through the inverse of the linear equivalence induced by the flipped perfect pairing. The resulting basis uses the same Fin 16 indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-paired-bases"),
                DeclarationHandle.Create(Prefix + "p48q_pair_bases"),
                H("The Gram matrix between the moving bases is the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every primitive complex cube root ζ and indices i,j in Fin 16, pairing the ith residue-one vector with the jth residue-two vector gives one when i = j and zero otherwise. These entries give the matching coefficients for creation and annihilation on the two fractional current grids."))),
                DescribeRole.Theorem))));
}

// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Automorphisms;

internal sealed class ReducibleActionWeightTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.";
    private static readonly LibraryNoteRef LatticeSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A proper nonzero invariant real Cartan subspace yields two independent fixed states of actual conformal weight two.",
        H("Fixed Weight-Two States from a Reducible Charge Action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reducible-charge-real-action"),
                DeclarationHandle.Create(Prefix + "realChargeAction"),
                H("Real extension of a charge automorphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For LatticeData D and an additive charge automorphism g, the real linear equivalence has matrix M with column j given by the coordinates of g applied to the j-th unit charge. The matrix for g⁻¹ gives the inverse."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reducible-charge-real-representation"),
                DeclarationHandle.Create(Prefix + "realChargeRepresentation"),
                H("Real Cartan representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the multiplicative group obtained from the additive automorphism group of the charge lattice, the real extension gives a representation on the real coordinate space. Charge coordinate expansion identifies matrix multiplication with composition of charge automorphisms."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reducible-charge-actual-omega-covariance"),
                DeclarationHandle.Create(Prefix + "actual_omega_covariance"),
                H("Actual quadratic covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource),
                Blocks(Paragraph(Text("Suppose the additive automorphism g preserves the integral bilinear form and the complex linear equivalence U preserves every actual integer mode. Suppose also that U sends each ground state at charge a to a unit scalar times the ground state at g(a). For every complex matrix A, U sends omega(D,A) to omega(D,MAMᵀ), where M is the complex matrix of g on the unit charges. Opposite-charge products recover the same current action as the canonical lift. Each quadratic is a sum of actual mode-minus-one products of those currents, so its image is determined by that current action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reducible-charge-fixed-weight-two"),
                DeclarationHandle.Create(Prefix + "reducible_action_fixed_weight_two"),
                H("Two independent fixed weight-two states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource),
                Blocks(Paragraph(Text("Assume the real Gram matrix is positive definite. Take indexed charge isometries g(t) and compatible complex equivalences U(t) satisfying the mode and ground-line hypotheses above for every t. If a proper nonzero real subspace W is invariant under every real extension of g(t), there are matrices H and P with H gramComplex(D) = 1. The ordered pair omega(D,PH), omega(D,H) lies in grade two, is linearly independent over ℂ and is fixed pointwise by each U(t). Mode one of the field of omega(D,H) multiplies both states by two. The Gram-orthogonal projector onto W provides P, and its commutation and self-adjointness give the required quadratic invariance."))),
                DescribeRole.Theorem))));
}

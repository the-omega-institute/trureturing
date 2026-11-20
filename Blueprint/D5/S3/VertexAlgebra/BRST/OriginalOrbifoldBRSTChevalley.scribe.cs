using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class OriginalOrbifoldBRSTChevalleyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTChevalley";

    private static DocumentBlock Node(
        string name, string heading, DescribeRole role, string statement) =>
        Describe.Lean(
            DescribeId.Create("original-orbifold-brst-chevalley-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charge reversal in the Golay–Leech relative BRST Lie algebra",
        H("Charge reversal in the relative BRST Lie algebra"),
        Blocks(
            Paragraph(Text("Borcherds (1992), Section 6, induces the Monster Lie algebra involution from the identity on the Monster vertex algebra and charge reversal on the hyperbolic lattice vertex algebra. On the relative BRST complex the ghost factor is fixed as well. The tensor action commutes with the differential and descends to the ghost-number-one Lie algebra.")),
            Node("stateTheta", "Charge reversal on states", DescribeRole.Definition,
                "Tensor the identity on the original Golay–Leech orbifold and on the bc Fock space with the native lattice involution on the hyperbolic factor."),
            Node("stateTheta_involutive", "Involution on states", DescribeRole.Theorem,
                "The tensor action squares to the identity on the entire algebraic state space."),
            Node("stateTheta_mode", "Equivariance of every field mode", DescribeRole.Theorem,
                "For all states s and x and every integer n, θ(sₙx) = (θs)ₙ(θx). Each of the two tensor state-field constructions is pointwise a finite convolution, whose hyperbolic coefficients obey the native lattice covariance."),
            Node("stateTheta_Q", "BRST equivariance", DescribeRole.Theorem,
                "The BRST current is fixed because the hyperbolic stress is quadratic in the odd oscillators. Its zero mode is the original BRST differential Q and therefore commutes with θ."),
            Node("stateTheta_b", "Antighost equivariance", DescribeRole.Theorem,
                "Every b mode commutes with θ since it acts on the ghost factor alone."),
            Node("stateTheta_L0", "Total energy equivariance", DescribeRole.Theorem,
                "The total conformal state is fixed. Its normalized mode 1 is total L₀ and commutes with θ."),
            Node("stateTheta_N", "Ghost-number equivariance", DescribeRole.Theorem,
                "The lifted ghost-number operator commutes with θ."),
            Node("stateTheta_descent", "Covariance of BRST descent", DescribeRole.Theorem,
                "The state descent applies the zero mode of b₋₁x to y. Commutation with b₋₁ and equivariance of that mode give θ(descent(x,y)) = descent(θx,θy)."),
            Node("stateTheta_momentumZeroMode", "Odd momentum coordinate operators", DescribeRole.Theorem,
                "The Heisenberg current dual to each hyperbolic momentum coordinate changes sign. Its zero mode anticommutes with θ."),
            Node("stateTheta_mem_fixedMomentum", "Momentum reversal on states", DescribeRole.Theorem,
                "A state of hyperbolic momentum p is sent to a state of momentum −p, as detected by the two momentum zero modes."),
            Node("chevalley", "Lie automorphism on the physical algebra", DescribeRole.Definition,
                "Commutation with b₀ and L₀ preserves the relative states. Commutation with Q preserves the relative cycles and images of relative primitives. The quotient map restricts by ghost number, preserves the existing descent bracket and has itself as its inverse."),
            Node("chevalley_involutive", "Involution on relative classes", DescribeRole.Theorem,
                "Applying the Lie automorphism twice fixes every relative ghost-number-one class."),
            Node("chevalley_mem_physicalMomentum_iff", "Exchange of opposite momentum spaces", DescribeRole.Theorem,
                "For every integral hyperbolic momentum p, the image of a degree-one class lies in momentum −p exactly when the original class lies in momentum p."),
            Node("chevalley_h", "Sign on the Cartan generators", DescribeRole.Theorem,
                "The two Cartan classes change sign because their Heisenberg states are odd under θ and θ commutes with c(1)."),
            Node("chevalley_eq_neg_of_zero_momentum", "Sign on the full Cartan", DescribeRole.Theorem,
                "The two current classes span the entire momentum-zero part of degree one. On this subspace the automorphism is multiplication by −1."))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class OriginalOrbifoldBRSTContravariantDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTContravariant";

    private static DocumentBlock Node(
        string name, string heading, DescribeRole role, string statement) =>
        Describe.Lean(
            DescribeId.Create("original-orbifold-brst-contravariant-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The contravariant form on the Golay–Leech relative BRST Lie algebra",
        H("The contravariant form on the relative BRST Lie algebra"),
        Blocks(
            Paragraph(Text("Write B for the physical BPZ pairing on relative ghost-number-one classes and θ for the native charge reversal. The sign of the contravariant form is the one in Borcherds (1992), Theorem 6.1.")),
            Node("physicalBPZ_chevalley", "BPZ isometry", DescribeRole.Theorem,
                "For all degree-one classes x and y, B(θx, θy) = B(x, y). On nonzero opposite momenta the bracket gives the BPZ scalar times a Cartan vector. That vector changes sign with the momentum and under θ, and its pairings with the Cartan generators recover the momentum coordinates. Momentum orthogonality handles nonopposite pairs, and θ negates both inputs at momentum zero. The direct sum extends the homogeneous identities by bilinearity."),
            Node("contravariantBPZ", "Contravariant form", DescribeRole.Definition,
                "The complex bilinear form C is obtained by precomposing physical BPZ in its second argument with θ and negating the result."),
            Node("contravariantBPZ_apply", "Evaluation of the form", DescribeRole.Theorem,
                "For all degree-one classes x and y, C(x, y) = −B(x, θy)."),
            Node("contravariantBPZ_symmetric", "Symmetry", DescribeRole.Theorem,
                "For all degree-one classes x and y, C(x, y) = C(y, x), by BPZ symmetry and the involutive BPZ isometry."),
            Node("contravariantBPZ_nondegenerate", "Nondegeneracy", DescribeRole.Theorem,
                "Both radicals of C vanish because physical BPZ has zero left and right radicals and θ is bijective."),
            Node("contravariantBPZ_eq_zero_of_momentum_ne", "Orthogonality of distinct momenta", DescribeRole.Theorem,
                "If x has momentum p and y has momentum q with q different from p, then C(x, y) = 0."),
            Node("contravariantBPZ_lie_adjoint", "Adjoint action", DescribeRole.Theorem,
                "For all degree-one classes a, x and y, C([a, x], y) = −C(x, [θa, y]). BPZ invariance and Lie skew symmetry give the sign, and involutivity and bracket covariance identify the second bracket."))));
}

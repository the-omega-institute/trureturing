using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiConstantBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiConstantBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The roots over distinct complex coordinates suffice to recover the signed matching polynomial up to a nonzero scalar.",
        H("From admissible constant matrices to a polynomial identity"),
        Blocks(
            Theorem("F_ne_zero", "Nonzero signed polynomial",
                "The first-coordinate coefficient is nonzero in each of the two size ranges."),
            Theorem("affine_polynomial_scalar", "Scalar rigidity on the injective zero locus",
                "Use the linear root to remove the first coordinate wherever the coefficient and collision factors are nonzero. Polynomial evaluation then gives the cross-multiplied identity. Relative primeness gives polynomial divisibility, and equality of total degrees makes the quotient a nonzero scalar."),
            Theorem("admissible_constant_matrix_scalar", "The constant-matrix bridge",
                "Preservation on all admissible rational-function matrices yields the scalar identity by applying the affine zero-locus argument to the admissible constant matrices."))));

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-constantbridge-" + name.ToLowerInvariant().Replace('_', '-');
}

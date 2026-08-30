using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenRationalShellRigidityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenCoding/GoldenRationalShellRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Positive golden-shell powers cannot create rational shell collisions.",
            H("Golden Rational Shell Rigidity"),
            Blocks(
                Theorem(
                    "positive-golden-powers-are-irrational",
                    "golden_ratio_positive_power_irrational",
                    "Positive Golden Powers Are Irrational",
                    "Every strictly positive natural power of the golden ratio is irrational."),
                Theorem(
                    "positive-golden-square-powers-are-irrational",
                    "golden_square_positive_power_irrational",
                    "Positive Golden Square Powers Are Irrational",
                    "Every positive natural power of the orientation-preserving unit phi squared is irrational."),
                Theorem(
                    "rational-shell-collision-forces-zero-depth",
                    "rational_shell_collision_implies_zero",
                    "Rational Shell Collision Forces Zero Depth",
                    "A nonzero rational scale cannot remain rational after a positive golden-shell translation unless the depth is zero."),
                Theorem(
                    "rational-shell-collision-is-the-identity",
                    "rational_shell_collision_rigidity",
                    "Rational Shell Collision Is the Identity",
                    "The only golden-shell collision between nonzero rational scales is the zero-depth identity collision."),
                Theorem(
                    "rational-golden-coordinates-have-no-positive-shell-collision",
                    "rational_coordinate_shell_rigidity",
                    "Rational Golden Coordinates Have No Positive Shell Collision",
                    "If two positive rational scales have golden coordinates differing by a natural number of shells, that number is zero and the scales agree."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(paragraph)),
                Paragraph(Text(
                    "This is an exact algebraic statement on the universal cover. "
                        + "No finite-precision separation estimate is claimed."))),
            DescribeRole.Theorem);
}

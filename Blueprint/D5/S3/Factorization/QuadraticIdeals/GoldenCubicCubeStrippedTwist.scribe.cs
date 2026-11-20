using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicCubeStrippedTwistDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact cubic-block quadratic twist removes the cube factor from the discriminant.",
        H("The exact cube-stripped elliptic twist"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-cube-stripped-exact-twist"),
                DeclarationHandle.Create(Module + "is_twist_stripped"),
                H("The twist and scaling remove the cubic part from the short model"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Writing the block as C cubed times R, the C-twist followed by the admissible scaling "
                    + "with unit C has coefficients minus three C R and two R L."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-cube-stripped-good-at-cube-prime"),
                DeclarationHandle.Create(Module + "square_cube_twist_good_at_cube_prime"),
                H("The hypothetical square-cube case has good reduction at the cube prime after twisting"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The stripped discriminant is the square of seventy-two times the square-role factor "
                    + "squared, hence nonzero at the distinct cube-role prime above three. This conditional "
                    + "model change does not exclude that factorization."))),
                DescribeRole.Theorem))));
}

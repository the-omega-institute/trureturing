using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicSquareRoleNineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original square-times-cube Lucas block forces exact congruences on its square prime.",
        H("Exact modulo-nine coordinates of the square-role Eisenstein factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-square-primary-coordinate-nine"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.primary_square_coordinates_nine"),
                H("The primary square coordinates are forced"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cube of a primary element is one modulo nine. Thus the original "
                    + "product fixes both coordinates of the primary square factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-actual-square-coordinates-nine"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine.actual_square_role_coordinates_nine"),
                H("The proposed native factorization forces an oriented norm representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the square-root-minus-three basis the two integral coordinates must "
                    + "be four and eight modulo nine, respectively. The witness divides the "
                    + "actual oriented Lucas element. The argument uses the native primary "
                    + "prime-ideal product, rather than assuming a proposed coordinate tuple."))),
                DescribeRole.Theorem))));
}

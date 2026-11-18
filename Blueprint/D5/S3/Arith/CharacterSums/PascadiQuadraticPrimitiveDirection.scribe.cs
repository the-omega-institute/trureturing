using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiQuadraticPrimitiveDirectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A primitive integer direction retains the original weights of a collinear coefficient family.",
        H("The leading direction of the actual quadratic pencil"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-quadratic-leading-primitive-direction"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiQuadraticPrimitiveDirection.quadratic_coefficient_primitive_direction"),
                H("One primitive direction with a common finite height"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let m,s be three integer coefficient rows, with a nonzero baseline pair, and suppose m0*si-mi*s0=0 for every row. For J>=1 and the actual bounds |mi|<=3J, |si|<=J squared, construct relatively prime integers d,n, integers ki, and D>=0 such that mi=d*ki, si=n*ki, every |ki|<=D, |d|D<=3J, |n|D<=J squared, and D<=3J squared.")),
                    Paragraph(Text("Normalize the baseline by its positive integer gcd. Bezout coefficients recover all ki without dividing by an individual leading entry. Choose D as the maximum of the three absolute values; either nonzero primitive direction coordinate has absolute value at least one. This retains zero entries and both coordinate axes.")),
                    Paragraph(Text("This is an auxiliary result used by the actual quadratic-resultant theorem. It does not count endpoint tuples or assert an improved range for Pascadi's full conjecture. Gcd normalization and Bezout are classical ingredients."))),
                DescribeRole.Theorem))));
}

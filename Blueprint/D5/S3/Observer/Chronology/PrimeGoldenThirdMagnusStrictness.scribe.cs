using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenThirdMagnusStrictnessDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenThirdMagnusStrictness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit prime-golden step-two fiber is separated by a nonzero primitive third Magnus coordinate.",
        H("Prime-Golden Third-Magnus Strictness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-third-magnus-strictness"),
                DeclarationHandle.Create(
                    Prefix + "explicit_prime_golden_third_magnus_strictness"),
                H("A primitive third coordinate escapes a complete second-Magnus fiber"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ABBA and BAAB prime-golden histories agree in bidegree, complete scalar Euler trajectory, and the full doubled degree-two Magnus coordinate.")),
                    Paragraph(Text(
                        "Their duodecupled degree-three Magnus difference is twelve times the cubic free-Lie defect and evaluates on E12 and E21 to the explicit nonzero matrix with off-diagonal entries twenty-four and minus twenty-four.")),
                    Paragraph(Text(
                        "This proves that the strict degree-three refinement survives logarithmic projection from tensor signature data to primitive Lie chronology."))),
                DescribeRole.Theorem))));
}

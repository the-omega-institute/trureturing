using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenStepThreeStrictnessDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenStepThreeStrictness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete prime-golden chronology lies in one complete step-two fiber and is separated by the full step-three Chen signature.",
        H("Prime-Golden Step-Three Strictness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-step-three-strict-refinement"),
                DeclarationHandle.Create(
                    Prefix + "explicit_prime_golden_step_three_strict_refinement"),
                H("Degree three strictly refines a genuine step-two fiber"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ABBA and BAAB histories have equal prime-golden bidegree, equal scalar Euler trajectory at every time, and equal complete step-two truncation.")),
                    Paragraph(Text(
                        "Their sextupled degree-three difference is six times the free-Lie chronology defect. The E12 and E21 representation evaluates it to the explicit nonzero matrix with off-diagonal entries twelve and minus twelve.")),
                    Paragraph(Text(
                        "Thus the degree-three-to-degree-two truncation homomorphism is not injective, with a fully explicit nontrivial fiber certificate."))),
                DescribeRole.Theorem))));
}

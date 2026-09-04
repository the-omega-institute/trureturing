using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenThirdOrderChronologyEscapeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two prime-golden words can share bidegree, complete scalar trajectory, and the full step-two signature while a cubic ordered moment separates their chronology.",
        H("Prime-Golden Third-Order Chronology Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-third-order-chronology-escape"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_third_order_chronology_escape"),
                H("A cubic ordered moment escapes a nontrivial step-two fiber"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The words ABBA and BAAB contain the same event multiset, have the same prime-golden bidegree, and give the same complete scalar Euler trajectory.")),
                    Paragraph(Text(
                        "Their full step-two chronological signatures agree in every associative ring representation.")),
                    Paragraph(Text(
                        "Whenever the displayed cubic ordered products differ, a degree-three moment distinguishes the two histories. This supplies an explicit boundary of step-two Magnus reconstruction."))),
                DescribeRole.Theorem))));
}

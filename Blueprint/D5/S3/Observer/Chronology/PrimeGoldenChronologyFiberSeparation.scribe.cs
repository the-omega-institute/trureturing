using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenChronologyFiberSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenChronologyFiberSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar prime-golden observation is constant on a bidegree fiber, while a noncommutative second-Magnus readout can separate chronology inside that fiber.",
        H("Prime-Golden Chronology Fiber Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-chronology-fiber-separation"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_chronology_fiber_separation"),
                H("Magnus separates swapped histories hidden by scalar observation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A fixed-prime scalar endpoint factors through the prime-event and short-step bidegree, so every word in one bidegree fiber has the same complete scalar trajectory.")),
                    Paragraph(Text(
                        "A two-event word and its reversal share that bidegree and scalar trajectory.")),
                    Paragraph(Text(
                        "When the two oriented commutators differ, the degree-two Magnus coordinate distinguishes the reversed histories inside the same scalar fiber."))),
                DescribeRole.Theorem))));
}

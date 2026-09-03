using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class PrimeZeckendorfFrequencyRigidityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/EulerGerm/PrimeZeckendorfFrequencyRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The calibrated first golden frequency removes abstract prime-relabeling freedom, "
            + "and finite rational prime superpositions retain unique coefficients.",
        H("Prime-Zeckendorf Frequency Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "first-excited-frequency-separates-prime-relabelings"),
                DeclarationHandle.Create(
                    Prefix + "first_excited_frequency_separates_prime_relabelings"),
                H("First excited frequency separates prime relabelings"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("SeparatesPrimeRelabelings")),
                    Open,
                    Operatorname, Grp(F.Id("firstExcitedFrequencyReadout")),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first excited frequency is phi squared times log p. Equality of "
                            + "this calibrated value forces equality of the prime channel, so "
                            + "an invariant prime relabeling fixes every prime.")),
                    Paragraph(Text(
                        "The same module proves that pairing this frequency with the canonical "
                            + "Zeckendorf layer address is faithful and that the complete first-"
                            + "frequency family is rationally linearly independent. These are "
                            + "arithmetic rigidity statements; they do not derive log p from a "
                            + "cut-and-project carrier."))),
                DescribeRole.Theorem))));
}

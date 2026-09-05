using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeWordAntipodeParityStepBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeWordAntipodeParityStepBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-word time reversal retains ordered information in the Magnus lift, leaves Liouville factor parity after commutative readout, and preserves the reversed golden step total and scalar endpoint.",
        H("Prime-Word Antipode, Parity, and Golden-Step Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-word-time-reversal-readout-trichotomy"),
                DeclarationHandle.Create(
                    Prefix + "prime_word_time_reversal_readout_trichotomy"),
                H("Three readouts of prime-step time reversal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("A")), Open, F.Id("w"), Close,
                    Eq, LambdaLower, Open, F.Id("n"), Close, Sp,
                    Operatorname, Grp(F.Id("R")), Open, F.Id("w"), Close,
                    Comma, RowBreak, Grp(),
                    Operatorname, Grp(F.Id("Step")), Open,
                    F.Id("rev"), Open, F.Id("w"), Close, Close,
                    Eq, Operatorname, Grp(F.Id("Step")), Open, F.Id("w"), Close,
                    Comma, RowBreak, Grp(),
                    Omega, Underscore, Grp(D(2)), Open,
                    F.Id("S"), Open, F.Id("w"), Close, Close,
                    Eq, Minus, Omega, Underscore, Grp(D(2)),
                    Open, F.Id("w"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The chronological Hopf antipode reverses the event word and negates every observed primitive increment. Under a commutative integer readout the reversal disappears, while the degree sign remains and equals the Liouville value of the represented prime product.")),
                    Paragraph(Text(
                        "The same event stream carries an independent Zeckendorf least-index parity. It selects the long phi-squared or short phi prime-local step. Reversing the list preserves its total frequency and terminal scalar phase, whereas the step-two Magnus coordinate changes sign.")),
                    Paragraph(Text(
                        "The companion theorems separate the Mobius channel as Liouville parity restricted to squarefree products, with nonsquarefree products sent to zero. No identification of factor-count parity with Zeckendorf parity is asserted."))),
                DescribeRole.Theorem))));
}

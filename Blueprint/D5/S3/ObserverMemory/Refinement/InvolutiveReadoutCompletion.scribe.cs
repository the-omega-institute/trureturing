using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class InvolutiveReadoutCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A readout flipped by an involution at every step is restored at even depth and remains visibly flipped at odd depth.",
        H("Involutive Readout Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("even-iterate-completes-readout"),
                DeclarationHandle.Create(Prefix + "even_iterate_completes_readout"),
                H("Even iterates complete the chosen readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Even")), Open, F.Id("n"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("readout")),
                    Open, Operatorname, Grp(F.Id("step")), Caret, F.Id("n"),
                    Open, F.Id("state"), Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("readout")), Open, F.Id("state"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When one update applies an involution to the selected readout, every even number of updates restores that readout.")),
                    Paragraph(Text(
                        "The state update itself need not be involutive, so readout completion does not imply return of the complete hidden state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-iterate-breaks-readout"),
                DeclarationHandle.Create(Prefix + "odd_iterate_breaks_readout"),
                H("Odd iterates preserve a visible flip"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Operatorname, Grp(F.Id("Odd")), Open, F.Id("n"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("flip")),
                    Open, Operatorname, Grp(F.Id("readout")), Open, F.Id("state"), Close, Close,
                    Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("readout")), Open, F.Id("state"), Close,
                    Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("readout")),
                    Open, Operatorname, Grp(F.Id("step")), Caret, F.Id("n"),
                    Open, F.Id("state"), Close, Close,
                    Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("readout")), Open, F.Id("state"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the starting readout is not fixed by the involution, every odd iterate is distinguished from the starting readout.")),
                    Paragraph(Text(
                        "This is the reusable formal core of the phrase odd breaking and even completion. It applies only to an explicitly involutive readout."))),
                DescribeRole.Theorem))));
}

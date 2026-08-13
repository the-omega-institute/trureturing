using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class CyclicWindowRevivalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "A full loop restores both generators of a finite cyclic observer window.",
            H("Cyclic Window Revival"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("cyclic-window-generators-recur"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/CyclicWindowRevival."
                        + "cyclic_window_generators_recur"),
                    H("Cyclic window generators recur after one full loop"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("S"), Caret, Grp(F.Id("M")), Sp, Eq, Sp, D(1), Sp,
                        Land, Sp, F.Id("C"), Caret, Grp(F.Id("M")), Sp, Eq, Sp,
                        D(1), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a finite observer window of size M, the address shift and phase "
                        + "clock each return to the identity after M updates. Together these "
                        + "recurrences certify perfect revival after a full cyclic loop. This "
                        + "statement is confined to the cyclic branch and does not claim a "
                        + "classification of revival scores in other branches."))),
                    DescribeRole.Theorem))));
}

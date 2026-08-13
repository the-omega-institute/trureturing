using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class RevivalSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Consecutive Fibonacci return scales converge to the golden ratio.",
            H("Fibonacci Return Ratio"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fibonacci-return-ratio-tends-to-golden-ratio"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/RevivalSpectrum.fibonacci_return_ratio_tendsto"),
                    H("Fibonacci return ratio tends to the golden ratio"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                        Frac, Grp(F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1))),
                        Grp(F.Id("F"), Underscore, F.Id("n")), Sp, Eq, Sp, Varphi, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The ratio of consecutive Fibonacci return scales converges to the "
                        + "golden ratio. This is the formalized return-spectrum clause; the "
                        + "remaining revival grading claims are outside this declaration."))),
                    DescribeRole.Theorem))));
}

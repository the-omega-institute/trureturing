using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class EntireZeroSetDichotomyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An entire function is identically zero or has a discrete zero set.",
        H("The Isolated-Zero Dichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("entire-functions-are-zero-or-have-discrete-zero-sets"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/EntireZeroSetDichotomy.entire_zero_set_dichotomy"),
                H("Entire functions are zero or have discrete zero sets"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), Colon, Mathbb, Grp(F.Id("C")), To,
                    Mathbb, Grp(F.Id("C")), Comma, RowBreak,
                    Operatorname, Grp(F.Id("AnalyticOnNhd")), Underscore,
                    Grp(Mathbb, Grp(F.Id("C"))), Open, F.Id("f"), Comma,
                    Mathbb, Grp(F.Id("C")), Close, Sp, Rightarrow, Sp,
                    F.Id("f"), Eq, D(0), Sp, Lor, Sp,
                    Operatorname, Grp(F.Id("IsDiscrete")), Open,
                    OpenBrace, F.Id("z"), InMacro, Mathbb, Grp(F.Id("C")), Sp,
                    Mid, Sp, F.Id("f"), Open, F.Id("z"), Close, Eq, D(0),
                    CloseBrace, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a complex function analytic on the whole plane, there are exactly "
                        + "two possibilities relevant here. It may vanish everywhere. Otherwise "
                        + "each zero is isolated, equivalently its zero set is discrete.")),
                    Paragraph(Text(
                        "Mathlib was searched before proving. The pinned library provides "
                        + "`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`, "
                        + "which gives the global isolated-zero dichotomy on a connected set. "
                        + "The Lean proof applies it to the complex plane and uses "
                        + "`compl_mem_codiscrete_iff` to translate the codiscrete complement "
                        + "into an explicitly discrete zero set.")),
                    Paragraph(Text(
                        "This formalization closes only the analytic mechanism stated in remark "
                        + "27.746, clause 2. It does not formalize the four motivating moduli-space "
                        + "examples, and it makes no claim about non-analytic relations, which the "
                        + "source explicitly places outside the scope of the isolation law."))),
                DescribeRole.Theorem))));
}

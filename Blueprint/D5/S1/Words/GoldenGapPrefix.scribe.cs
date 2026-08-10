using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenGapPrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Words/GoldenGapPrefix",
            "Establish the adjacent-prefix chain for finite Fibonacci and golden gap words."),
        H("Golden Gap Prefix Chain"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fibonacci-word-append-recurrence"),
                H("Fibonacci words satisfy the append recurrence"),
                LeanTheorem("D5/S1/Words/GoldenGapPrefix.fibWord_append_rec"),
                Disp(Seq(
                    Forall, Sp, F.Id("Q"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Plus, D(2), Close,
                    Eq, Operatorname, Grp(F.Id("append")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Plus, D(1), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The finite Fibonacci word at level Q plus two is the concatenation of "
                    + "the words at levels Q plus one and Q.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fibonacci-word-adjacent-prefix"),
                H("Adjacent Fibonacci words form a prefix chain"),
                LeanTheorem("D5/S1/Words/GoldenGapPrefix.fibWord_prefix_succ"),
                Disp(Seq(
                    Forall, Sp, F.Id("Q"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("prefix")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("fibWord")), Open,
                    F.Id("Q"), Plus, D(1), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Every finite Fibonacci word is a prefix of the word at the next level.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("golden-gap-word-adjacent-prefix"),
                H("Adjacent golden gap words form a prefix chain"),
                LeanTheorem("D5/S1/Words/GoldenGapPrefix.goldenGapWord_prefix_succ"),
                Disp(Seq(
                    Forall, Sp, F.Id("Q"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("Q"), Ge, D(2), Rightarrow, Sp,
                    Operatorname, Grp(F.Id("prefix")), Open,
                    Operatorname, Grp(F.Id("goldenGapWord")), Open, F.Id("Q"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("goldenGapWord")), Open,
                    F.Id("Q"), Plus, D(1), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "From level two onward, the frozen golden-gap tower identification "
                    + "transfers the Fibonacci prefix chain to consecutive golden gap "
                    + "words.")))))));
}

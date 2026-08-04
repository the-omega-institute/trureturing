using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ZeckendorfOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Words/ZeckendorfOrder",
            "Greatest-index-first Zeckendorf representations carry numerical order lexicographically."),
        H("Order on Zeckendorf Representations"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("zeckendorf-lexicographic-order-matches-fibonacci-sums"),
                H("Lexicographic order matches Fibonacci sums"),
                LeanTheorem(
                    "D5/S1/Words/ZeckendorfOrder.isZeckendorfRep_lex_iff_sum_fib_lt"),
                Disp(Seq(Operatorname, Grp(F.Id("IsZeck")), Open, F.Id("l"), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("IsZeck")), Open, F.Id("k"), Close, Sp, Implies, Sp, Left, Open, F.Id("l"), Sp, Lt, Underscore, Grp(F.Text, Grp(F.Id("lex"))), Sp, F.Id("k"), Sp, Iff, Sp, Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("l")), Sp, F.Id("F"), Underscore, F.Id("i"), Sp, Lt, Sp, Sum, Underscore, Grp(F.Id("j"), Sp, InMacro, Sp, F.Id("k")), Sp, F.Id("F"), Underscore, F.Id("j"), Right, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For two valid Zeckendorf index lists ordered from greatest index "
                    + "downward, strict lexicographic order is equivalent to strict order "
                    + "of the corresponding sums of Fibonacci numbers.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("canonical-zeckendorf-order-embedding"),
                H("Canonical Zeckendorf representations preserve strict order"),
                LeanTheorem(
                    "D5/S1/Words/ZeckendorfOrder.zeckendorf_lex_iff_lt"),
                Disp(Seq(Operatorname, Grp(F.Id("zeck")), Open, F.Id("m"), Close, Sp, Lt, Underscore, Grp(F.Text, Grp(F.Id("lex"))), Sp, Operatorname, Grp(F.Id("zeck")), Open, F.Id("n"), Close, Sp, Iff, Sp, F.Id("m"), Sp, Lt, Sp, F.Id("n"))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Mathlib's canonical Zeckendorf representation maps natural numbers "
                    + "to greatest-index-first lists so that list lexicographic order holds "
                    + "exactly when the original natural numbers are strictly ordered.")))))));
}

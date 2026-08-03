using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ZeckendorfOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Words/ZeckendorfOrder",
                "Greatest-index-first Zeckendorf representations carry numerical order lexicographically."),
            H("Order on Zeckendorf Representations"),
            Blocks(
                new DocumentBlock.Describe(
                    DescribeId.Create("zeckendorf-lexicographic-order-matches-fibonacci-sums"),
                    DescribeKind.Theorem,
                    H("Lexicographic order matches Fibonacci sums"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Words/ZeckendorfOrder.isZeckendorfRep_lex_iff_sum_fib_lt")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For two valid Zeckendorf index lists ordered from greatest index "
                        + "downward, strict lexicographic order is equivalent to strict order "
                        + "of the corresponding sums of Fibonacci numbers."))),
                    LatexStatement.Create(
                        @"$$\operatorname{IsZeck}(l) \land \operatorname{IsZeck}(k) \implies "
                        + @"\left(l <_{\text{lex}} k \iff \sum_{i \in l} F_i < \sum_{j \in k} F_j\right)$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("canonical-zeckendorf-order-embedding"),
                    DescribeKind.Theorem,
                    H("Canonical Zeckendorf representations preserve strict order"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Words/ZeckendorfOrder.zeckendorf_lex_iff_lt")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Mathlib's canonical Zeckendorf representation maps natural numbers "
                        + "to greatest-index-first lists so that list lexicographic order holds "
                        + "exactly when the original natural numbers are strictly ordered."))),
                    LatexStatement.Create(
                        @"$$\operatorname{zeck}(m) <_{\text{lex}} \operatorname{zeck}(n) \iff m < n$$")))));
}

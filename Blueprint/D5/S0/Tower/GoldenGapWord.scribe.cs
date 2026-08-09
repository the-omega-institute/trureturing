using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenGapWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");
        var word = Call("goldenGapWord", q);
        var fib = Call("fibWord", q);

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Tower/GoldenGapWord",
                "The full golden tower gap word is the Fibonacci substitution word."),
            H("Golden Gap Word"),
            Blocks(
                Paragraph(Text(
                    "The boundary-completed gap list carries more information than its two "
                    + "multiplicities: it records every large and small gap in the frozen Fin "
                    + "order. Refinement turns this ordered list into a Fibonacci word.")),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("oriented-fibonacci-replacement"),
                    H("Oriented Fibonacci replacement"),
                    LeanDefinition("D5/S0/Tower/GoldenGapWord.subst"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A large letter is replaced by large then small, while a small letter "
                        + "is replaced by one large letter.")))
                ),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("finite-fibonacci-word"),
                    H("Finite Fibonacci word"),
                    LeanDefinition("D5/S0/Tower/GoldenGapWord.fibWord"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Starting from one large letter, fibWord iterates the oriented "
                        + "replacement once per level.")))
                ),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("boundary-completed-golden-gap-word"),
                    H("Boundary-completed golden gap word"),
                    LeanDefinition("D5/S0/Tower/GoldenGapWord.goldenGapWord"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "This word is defined directly by List.ofFn over Fin(Fib(Q+2)). Each "
                        + "letter tests GoldenGapFrequency.fullGap at that exact index, so the "
                        + "last interval from the final name value to one is part of the word.")))
                ),
                DocumentBlock.Describe.Lemma(
                    DescribeId.Create("false-letter-is-the-small-gap"),
                    H("A false letter is the small gap"),
                    LeanTheorem("D5/S0/Tower/GoldenGapWord.golden_gap_false_iff_small"),
                    new Formula.Logic(
                        Equal(Call("gapLetter", q, Id("i")), Id("false")),
                        FormulaLogicOperator.Iff,
                        Equal(Call("fullGap", q, Id("i")), Call("smallGapLength", q))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The two-length spectrum rules out a third case: failing the large-gap "
                        + "test is equivalent to having the frozen small length.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("refinement-substitutes-the-complete-word"),
                    H("Refinement substitutes the complete word"),
                    LeanTheorem("D5/S0/Tower/GoldenGapWord.golden_gap_word_step"),
                    ForLevels(
                        q,
                        naturals,
                        Equal(
                            Call("flatMap", word, Id("subst")),
                            Call("goldenGapWord", Add(q, Num(1))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The equality is global and positional. The proof splits the complete "
                        + "fine Fin interval into its two Fibonacci blocks and proves the "
                        + "fullGap scaling on each block; the final upper-block index is the "
                        + "terminal boundary gap, so no suffix is omitted.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("full-gap-word-is-fibonacci"),
                    H("The full gap word is Fibonacci"),
                    LeanTheorem("D5/S0/Tower/GoldenGapWord.golden_full_gap_word"),
                    ForLevels(q, naturals, Equal(word, fib)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "From level two onward the word cut directly from the frozen tower is "
                        + "the recursively generated Fibonacci word. This is repo-derived new "
                        + "reasoning: the frozen frequency theorem follows mathematically by "
                        + "counting letters, but that module and its ledger node remain unchanged.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenGapFrequency")),
            ]));
    }

    private static Formula ForLevels(Formula q, Formula naturals, Formula conclusion) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(q, FormulaRelationOperator.GreaterThanOrEqual, Num(2)),
                FormulaLogicOperator.Implies,
                conclusion));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}

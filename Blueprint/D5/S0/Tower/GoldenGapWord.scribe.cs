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

        return DocumentDefinition.Create(ScribeNode.Create(
            "The full golden tower gap word is the Fibonacci substitution word.",
            H("Golden Gap Word"),
            Blocks(
                Paragraph(Text(
                    "The boundary-completed gap list carries more information than its two "
                    + "multiplicities: it records every large and small gap in the frozen Fin "
                    + "order. Refinement turns this ordered list into a Fibonacci word.")),
                Describe.Lean(
                    DescribeId.Create("oriented-fibonacci-replacement"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapWord.subst"),
                    H("Oriented Fibonacci replacement"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A large letter is replaced by large then small, while a small letter "
                        + "is replaced by one large letter."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("finite-fibonacci-word"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapWord.fibWord"),
                    H("Finite Fibonacci word"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Starting from one large letter, fibWord iterates the oriented "
                        + "replacement once per level."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("boundary-completed-golden-gap-word"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapWord.goldenGapWord"),
                    H("Boundary-completed golden gap word"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This word is defined directly by List.ofFn over Fin(Fib(Q+2)). Each "
                        + "letter tests GoldenGapFrequency.fullGap at that exact index, so the "
                        + "last interval from the final name value to one is part of the word."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("false-letter-is-the-small-gap"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapWord.golden_gap_false_iff_small"),
                    H("A false letter is the small gap"),
                    StatementSource.FromAuthor(new Formula.Logic(
                        Equal(Call("gapLetter", q, Id("i")), Id("false")),
                        FormulaLogicOperator.Iff,
                        Equal(Call("fullGap", q, Id("i")), Call("smallGapLength", q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The two-length spectrum rules out a third case: failing the large-gap "
                        + "test is equivalent to having the frozen small length."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("refinement-substitutes-the-complete-word"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapWord.golden_gap_word_step"),
                    H("Refinement substitutes the complete word"),
                    StatementSource.FromAuthor(ForLevels(
                        q,
                        naturals,
                        Equal(
                            Call("flatMap", word, Id("subst")),
                            Call("goldenGapWord", Add(q, Num(1)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The equality is global and positional. The proof splits the complete "
                        + "fine Fin interval into its two Fibonacci blocks and proves the "
                        + "fullGap scaling on each block; the final upper-block index is the "
                        + "terminal boundary gap, so no suffix is omitted."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("full-gap-word-is-fibonacci"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapWord.golden_full_gap_word"),
                    H("The full gap word is Fibonacci"),
                    StatementSource.FromAuthor(ForLevels(q, naturals, Equal(word, fib))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "From level two onward the word cut directly from the frozen tower is "
                        + "the recursively generated Fibonacci word. This is repo-derived new "
                        + "reasoning: the frozen frequency theorem follows mathematically by "
                        + "counting letters, but that module and its ledger node remain unchanged."))),
                    DescribeRole.Theorem)),
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
}

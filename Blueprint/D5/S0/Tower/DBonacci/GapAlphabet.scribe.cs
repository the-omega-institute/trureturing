using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciGapAlphabetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var q = Id("Q");
        var i = Id("i");
        var letter = Id("letter");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite d-bonacci gap letters carry the exact local refinement substitution.",
            H("D-Bonacci Gap Alphabet"),
            Blocks(
                Paragraph(Text(
                    "The gap labels zero through d minus one form a finite alphabet. "
                    + "Zero is replaced by the top letter; every successor is replaced "
                    + "by the top letter followed by its predecessor.")),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-gap-letter-type"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/GapAlphabet.DBonacciGapLetter"),
                    H("Finite gap alphabet"),
                    StatementSource.FromAuthor(Equal(
                        Call("GapLetter", d),
                        Call("Fin", d))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Using Fin d makes the allowed label bound part of the type."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-gap-letter-substitution-map"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/GapAlphabet.gapLetterSubstitution"),
                    H("Gap-letter substitution"),
                    StatementSource.FromAuthor(Equal(
                        Call("substitute", d, letter),
                        Call("zeroOrSuccessorReplacement", d, letter))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The replacement stays in Fin d: its first letter is d minus one, "
                        + "and a nonzero input contributes its predecessor second."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("general-d-bonacci-gap-letter-substitution"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/GapAlphabet.dbonacci_gap_letter_substitution"),
                    H("General typed gap substitution"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("i"),
                        Call("coarseGapIndex", d, q),
                        Equal(
                            Call("refinementWord", d, q, i),
                            Call("substitute", d, Call("coarseGapLetter", d, q, i))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For d at least two, the existing local metric theorem supplies the "
                        + "coarse letter and proves that the fine interval realizes precisely "
                        + "its one- or two-letter replacement word."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-three-gap-substitution-equality"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/GapAlphabet.dbonacciGapLetterSubstitution_three_eq_tribonacciGapLetterSubstitution"),
                    H("Order-three substitution equality"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("letter"),
                        Call("Fin", Num(3)),
                        Equal(
                            Call("mapToTribonacci", Call("substitute", Num(3), letter)),
                            Call("tribonacciSubstitute", Call("mapToTribonacci", letter))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The equivalence sends labels zero, one, and two to small, combined, "
                        + "and large. Transporting the typed substitution across it gives the "
                        + "frozen Tribonacci substitution exactly."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-three-geometric-substitution-consistency"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/GapAlphabet.dbonacci_gap_letter_substitution_three_consistent_with_tribonacci"),
                    H("Order-three geometric consistency"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("i"),
                        Call("coarseGapIndex", Num(3), q),
                        Equal(
                            Call("transportedRefinementWord", q, i),
                            Call("tribonacciSubstitute", Call("transportedCoarseLetter", q, i))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This corollary takes the witness produced by the general geometric "
                        + "theorem and proves that its transported word is the frozen replacement "
                        + "word, so the specialization is not a second source."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/Substitution")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Substitution")),
            ]));
    }
}

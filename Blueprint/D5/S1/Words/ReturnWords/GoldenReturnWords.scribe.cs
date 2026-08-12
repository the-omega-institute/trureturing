using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class GoldenReturnWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Define golden return words, prove existence for every occurring factor, and "
            + "classify the two return words of each length-one factor.",
        H("Return Words of the Golden Word: the Length-One Case"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjacent-golden-occurrences"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "AdjacentGoldenOccurrences"),
                H("Adjacent occurrences have no intervening start"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "AdjacentGoldenOccurrences n w i j means that i is strictly before j, "
                    + "the length-n golden factors at both starts equal w, and no start "
                    + "strictly between i and j carries the same factor."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("golden-return-word-predicate"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords.IsGoldenReturnWord"),
                H("A return word is the block between adjacent starts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A list r is a return word to w when adjacent occurrences of w start at "
                    + "i and j and r is the golden factor of length j-i beginning at i."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("golden-return-word-set"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords.goldenReturnWords"),
                H("Return words are collected as a set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "goldenReturnWords n w is the set of all lists satisfying the return-word "
                    + "predicate. Finiteness is proved here only for length one."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("every-occurring-factor-has-a-return-word"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_nonempty"),
                H("Every occurring golden factor has a return word"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("w"), InMacro,
                    Operatorname, Grp(F.Id("goldenFactorSet")), Open, F.Id("n"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    F.Id("n"), Comma, F.Id("w"), Close, Neq, Emptyset))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Recurrence supplies an occurrence later than a chosen start. Nat.find "
                    + "selects the least such later start; its minimality excludes every "
                    + "intermediate occurrence and therefore supplies an adjacent pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("true-factor-return-words"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_true"),
                H("The true factor has return words T and TF"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    D(1), Comma, F.Id("T"), Close, Eq,
                    OpenBrace, F.Id("T"), Comma, F.Id("TF"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Balance rules out two consecutive false letters by comparison with the "
                    + "known TT window. Hence adjacent true starts differ by one or two, "
                    + "giving T and TF. Starts (2,3) and (0,2) realize both cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("false-factor-return-words"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_false"),
                H("The false factor has return words FT and FTT"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    D(1), Comma, F.Id("F"), Close, Eq,
                    OpenBrace, F.Id("FT"), Comma, F.Id("FTT"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The absence of FF forces a true letter between false starts. Balance "
                    + "also rules out TTT by comparison with the known FTF window, so the "
                    + "gap is two or three. Starts (4,6) and (1,4) realize both values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("length-one-factors-have-two-return-words"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_encard_eq_two"),
                H("Every length-one factor has exactly two return words"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("w"), InMacro,
                    Operatorname, Grp(F.Id("goldenFactorSet")), Open, D(1), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("encard")), Open,
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    D(1), Comma, F.Id("w"), Close, Close, Eq, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every member of goldenFactorSet 1 has length one, hence is T or F. "
                        + "The two explicit set equalities give extended cardinality two.")),
                    Paragraph(Text(
                        "The length-two occurrence-gap spectra are global: TF and FT have "
                        + "{2,3}, while TT has {3,5}; each therefore has encard two. This does "
                        + "not claim the all-n theorem. That theorem remains deferred until "
                        + "admissible_rotation_gap_first_returns_two is proved without new "
                        + "axioms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seed-substitution-preserves-synchronized-return-membership"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "seed_return_word_subst_mem"),
                H("Seed substitution preserves return membership at synchronized markers"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("r"), InMacro, Sp, F.Id("R"), Underscore, D(1), Open, F.Id("b"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("subst")), Open, F.Id("r"), Close,
                    InMacro, Sp, F.Id("R"), Underscore, D(2), Open,
                    Operatorname, Grp(F.Id("marker")), Open, F.Id("b"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For b=true the synchronized image marker is TF; for b=false it is TT. "
                    + "The marker is essential: the naive claim using subst(F)=T is false "
                    + "because subst(FT)=TTF is not a return word to T."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenUniformRecurrence")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenSubstFixed")),
        ]));
}

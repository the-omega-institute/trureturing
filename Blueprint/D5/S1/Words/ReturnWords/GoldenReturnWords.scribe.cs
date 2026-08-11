using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class GoldenReturnWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Words/ReturnWords/GoldenReturnWords",
            "Define golden return words, prove existence for every occurring factor, and "
            + "classify the two return words of each length-one factor."),
        H("Return Words of the Golden Word: the Length-One Case"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("adjacent-golden-occurrences"),
                H("Adjacent occurrences have no intervening start"),
                LeanDefinition(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "AdjacentGoldenOccurrences"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "AdjacentGoldenOccurrences n w i j means that i is strictly before j, "
                    + "the length-n golden factors at both starts equal w, and no start "
                    + "strictly between i and j carries the same factor.")))),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("golden-return-word-predicate"),
                H("A return word is the block between adjacent starts"),
                LeanDefinition(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords.IsGoldenReturnWord"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A list r is a return word to w when adjacent occurrences of w start at "
                    + "i and j and r is the golden factor of length j-i beginning at i.")))),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("golden-return-word-set"),
                H("Return words are collected as a set"),
                LeanDefinition(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords.goldenReturnWords"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "goldenReturnWords n w is the set of all lists satisfying the return-word "
                    + "predicate. Finiteness is proved here only for length one.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("every-occurring-factor-has-a-return-word"),
                H("Every occurring golden factor has a return word"),
                LeanTheorem(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_nonempty"),
                Disp(Seq(
                    F.Id("w"), InMacro,
                    Operatorname, Grp(F.Id("goldenFactorSet")), Open, F.Id("n"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    F.Id("n"), Comma, F.Id("w"), Close, Neq, Emptyset)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Recurrence supplies an occurrence later than a chosen start. Nat.find "
                    + "selects the least such later start; its minimality excludes every "
                    + "intermediate occurrence and therefore supplies an adjacent pair.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("true-factor-return-words"),
                H("The true factor has return words T and TF"),
                LeanTheorem(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_true"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    D(1), Comma, F.Id("T"), Close, Eq,
                    OpenBrace, F.Id("T"), Comma, F.Id("TF"), CloseBrace)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Balance rules out two consecutive false letters by comparison with the "
                    + "known TT window. Hence adjacent true starts differ by one or two, "
                    + "giving T and TF. Starts (2,3) and (0,2) realize both cases.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("false-factor-return-words"),
                H("The false factor has return words FT and FTT"),
                LeanTheorem(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_false"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    D(1), Comma, F.Id("F"), Close, Eq,
                    OpenBrace, F.Id("FT"), Comma, F.Id("FTT"), CloseBrace)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The absence of FF forces a true letter between false starts. Balance "
                    + "also rules out TTT by comparison with the known FTF window, so the "
                    + "gap is two or three. Starts (4,6) and (1,4) realize both values.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("length-one-factors-have-two-return-words"),
                H("Every length-one factor has exactly two return words"),
                LeanTheorem(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "golden_return_words_encard_eq_two"),
                Disp(Seq(
                    F.Id("w"), InMacro,
                    Operatorname, Grp(F.Id("goldenFactorSet")), Open, D(1), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("encard")), Open,
                    Operatorname, Grp(F.Id("goldenReturnWords")), Open,
                    D(1), Comma, F.Id("w"), Close, Close, Eq, D(2))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Every member of goldenFactorSet 1 has length one, hence is T or F. "
                        + "The two explicit set equalities give extended cardinality two.")),
                    Paragraph(Text(
                        "The length-two occurrence-gap spectra are global: TF and FT have "
                        + "{2,3}, while TT has {3,5}; each therefore has encard two. This does "
                        + "not claim the all-n theorem. That theorem remains deferred until "
                        + "admissible_rotation_gap_first_returns_two is proved without new "
                        + "axioms.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("seed-substitution-preserves-synchronized-return-membership"),
                H("Seed substitution preserves return membership at synchronized markers"),
                LeanTheorem(
                    "D5/S1/Words/ReturnWords/GoldenReturnWords."
                    + "seed_return_word_subst_mem"),
                Disp(Seq(
                    F.Id("r"), InMacro, Sp, F.Id("R"), Underscore, D(1), Open, F.Id("b"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("subst")), Open, F.Id("r"), Close,
                    InMacro, Sp, F.Id("R"), Underscore, D(2), Open,
                    Operatorname, Grp(F.Id("marker")), Open, F.Id("b"), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For b=true the synchronized image marker is TF; for b=false it is TT. "
                    + "The marker is essential: the naive claim using subst(F)=T is false "
                    + "because subst(FT)=TTF is not a return word to T."))))),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenUniformRecurrence")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenSubstFixed")),
        ]));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}

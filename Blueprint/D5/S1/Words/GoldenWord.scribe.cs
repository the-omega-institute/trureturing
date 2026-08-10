using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Words/GoldenWord",
            "Construct the infinite golden word as the coherent diagonal limit of finite tower words."),
        H("The Infinite Golden Word"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fibonacci-word-length"),
                H("Finite Fibonacci words have Fibonacci length"),
                LeanTheorem("D5/S1/Words/GoldenWord.fibWord_length"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("length")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Close, Close,
                    Eq, Operatorname, Grp(F.Id("Fib")), Open, F.Id("Q"), Plus, D(2), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The Zeckendorf realization of a level-Q word contains exactly Fib(Q+2) "
                    + "letters.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("diagonal-index-is-present"),
                H("Every diagonal index occurs at its own level"),
                LeanTheorem("D5/S1/Words/GoldenWord.index_lt_diagonal_level"),
                Disp(Seq(
                    F.Id("i"), Lt, Operatorname, Grp(F.Id("length")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("i"), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The Fibonacci lower bound makes index i a valid position in fibWord(i), "
                    + "so the diagonal construction is total.")))),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("golden-word-diagonal-limit"),
                H("The golden word is read on the tower diagonal"),
                LeanDefinition("D5/S1/Words/GoldenWord.goldenWord"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The letter at index i is the ith letter of the finite Fibonacci word at "
                    + "level i. This definition retains the finite tower as its construction.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-stage-coherence"),
                H("Every covering finite stage gives the same letter"),
                LeanTheorem("D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close, Eq,
                    Operatorname, Grp(F.Id("get")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Close,
                    Comma, F.Id("i"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Embedding both the diagonal stage and an arbitrary covering stage into a "
                    + "common later word proves that their ith entries agree.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("zeckendorf-letter-characterization"),
                H("Letters are characterized by the least Zeckendorf digit"),
                LeanTheorem("D5/S1/Words/GoldenWord.goldenWord_char_zeckendorf"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close,
                    Eq, F.Id("true"), Sp, Iff, Sp, Neg, Open, D(2), InMacro,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("i"), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A golden-word letter is true exactly when the least Zeckendorf weight is "
                    + "absent. This is a theorem about the diagonal tower definition, not a "
                    + "replacement definition.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("golden-gap-stage-coherence"),
                H("Frozen golden-gap stages give the same letters"),
                LeanTheorem("D5/S1/Words/GoldenWord.goldenWord_eq_goldenGapWord_get"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close, Eq,
                    Operatorname, Grp(F.Id("get")), Open,
                    Operatorname, Grp(F.Id("goldenGapWord")), Open, F.Id("Q"), Close,
                    Comma, F.Id("i"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "From level two onward, the frozen golden-gap identification transfers "
                    + "finite-stage coherence to the tower's gap words.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("golden-gap-full-prefix"),
                H("Each frozen golden-gap word is a full finite prefix"),
                LeanTheorem("D5/S1/Words/GoldenWord.goldenWord_prefix_eq_goldenGapWord"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("prefix")), Open,
                    Operatorname, Grp(F.Id("goldenWord")), Comma,
                    Operatorname, Grp(F.Id("goldenGapWord")), Open, F.Id("Q"), Close,
                    Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Collecting the coherent pointwise letters over the finite length recovers "
                    + "the entire frozen golden-gap word."))))),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Tower/GoldenGapZeckendorf")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenGapPrefix")),
        ]));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the infinite golden word as the coherent diagonal limit of finite tower words.",
        H("The Infinite Golden Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-word-length"),
                DeclarationHandle.Create("D5/S1/Words/GoldenWord.fibWord_length"),
                H("Finite Fibonacci words have Fibonacci length"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("length")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Close, Close,
                    Eq, Operatorname, Grp(F.Id("Fib")), Open, F.Id("Q"), Plus, D(2), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Zeckendorf realization of a level-Q word contains exactly Fib(Q+2) "
                    + "letters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-index-is-present"),
                DeclarationHandle.Create("D5/S1/Words/GoldenWord.index_lt_diagonal_level"),
                H("Every diagonal index occurs at its own level"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("i"), Lt, Operatorname, Grp(F.Id("length")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("i"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Fibonacci lower bound makes index i a valid position in fibWord(i), "
                    + "so the diagonal construction is total."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-word-diagonal-limit"),
                DeclarationHandle.Create("D5/S1/Words/GoldenWord.goldenWord"),
                H("The golden word is read on the tower diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The letter at index i is the ith letter of the finite Fibonacci word at "
                    + "level i. This definition retains the finite tower as its construction."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("finite-stage-coherence"),
                DeclarationHandle.Create("D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get"),
                H("Every covering finite stage gives the same letter"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close, Eq,
                    Operatorname, Grp(F.Id("get")), Open,
                    Operatorname, Grp(F.Id("fibWord")), Open, F.Id("Q"), Close,
                    Comma, F.Id("i"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Embedding both the diagonal stage and an arbitrary covering stage into a "
                    + "common later word proves that their ith entries agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeckendorf-letter-characterization"),
                DeclarationHandle.Create("D5/S1/Words/GoldenWord.goldenWord_char_zeckendorf"),
                H("Letters are characterized by the least Zeckendorf digit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close,
                    Eq, F.Id("true"), Sp, Iff, Sp, Neg, Open, D(2), InMacro,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("i"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A golden-word letter is true exactly when the least Zeckendorf weight is "
                    + "absent. This is a theorem about the diagonal tower definition, not a "
                    + "replacement definition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-gap-stage-coherence"),
                DeclarationHandle.Create("D5/S1/Words/GoldenWord.goldenWord_eq_goldenGapWord_get"),
                H("Frozen golden-gap stages give the same letters"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("i"), Close, Eq,
                    Operatorname, Grp(F.Id("get")), Open,
                    Operatorname, Grp(F.Id("goldenGapWord")), Open, F.Id("Q"), Close,
                    Comma, F.Id("i"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "From level two onward, the frozen golden-gap identification transfers "
                    + "finite-stage coherence to the tower's gap words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-gap-full-prefix"),
                DeclarationHandle.Create("D5/S1/Words/GoldenWord.goldenWord_prefix_eq_goldenGapWord"),
                H("Each frozen golden-gap word is a full finite prefix"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("prefix")), Open,
                    Operatorname, Grp(F.Id("goldenWord")), Comma,
                    Operatorname, Grp(F.Id("goldenGapWord")), Open, F.Id("Q"), Close,
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Collecting the coherent pointwise letters over the finite length recovers "
                    + "the entire frozen golden-gap word."))),
                DescribeRole.Theorem)),
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

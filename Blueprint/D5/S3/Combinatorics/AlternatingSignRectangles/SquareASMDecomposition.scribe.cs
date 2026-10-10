using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AlternatingSignRectangles;

internal sealed class SquareASMDecompositionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hongesberg2026asr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SquareASMDecomposition for extendably 312-avoiding alternating sign rectangles.",
        H("SquareASMDecomposition"), Blocks(
            Paragraph(Text("The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.")),
            Describe.Lean(DescribeId.Create("square-asmdecomposition-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.cons_zero_line"), H("cons_zero_line"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-asmdecomposition-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.cons_zero_ends"), H("cons_zero_ends"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-asmdecomposition-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.TopLeftFibre"), H("TopLeftFibre"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-asmdecomposition-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.topLeftFibre_card"), H("topLeftFibre_card"),
                StatementSource.FromAuthor(Formula3()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-asmdecomposition-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.avoidingASM_card_schroder"), H("avoidingASM_card_schroder"),
                StatementSource.FromAuthor(Formula4()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-asmdecomposition-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareASMDecomposition.S_diagonal"), H("S_diagonal"),
                StatementSource.FromAuthor(Formula5()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The square count is the large-Schröder number of index d − 1 for d > 0."))), DescribeRole.Lemma)), []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n"), Sp, To, Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(Named("Alternates"), Sp, F.Id("a"))), Sp, To, Sp, Parenthesized(Seq(Named("StartsOne"), Sp, F.Id("a"))), Sp, To, Sp, Named("Alternates"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Dot, Sp, Named("cons"), Sp, D(0), Sp, F.Id("a"))), Sp, Land, Sp, Named("StartsOne"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Dot, Sp, Named("cons"), Sp, D(0), Sp, F.Id("a")))));

    private static Formula Formula1() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n"), Sp, To, Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(Named("EndsOne"), Sp, F.Id("a"))), Sp, To, Sp, Named("EndsOne"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Dot, Sp, Named("cons"), Sp, D(0), Sp, F.Id("a")))));

    private static Formula Formula2() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("TopLeftFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Named("Type")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("TopLeftFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(new Formula.SetLiteral([Seq(F.Id("R"), Sp, Colon, Sp, Named("Counted"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))), Sp, Bar, Sp, F.Id("R"), Sp, Dot, Sp, Named("val"), Sp, D(0), Sp, D(0), Sp, Eq, Sp, D(1))])))]));

    private static Formula Formula3() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("TopLeftFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"))), Sp, Eq, Sp, F.Id("S"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d")));

    private static Formula Formula4() =>
        Disp(Seq(Forall, Sp, F.Id("n"), Sp, Comma, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("AvoidASM"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Eq, Sp, Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, F.Id("n")));

    private static Formula Formula5() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("d"))), Sp, To, Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("d"), Sp, F.Id("d"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Eq, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, D(1))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z")))))));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AlternatingSignRectangles;

internal sealed class EmptyRowFillingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hongesberg2026asr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "EmptyRowFilling for extendably 312-avoiding alternating sign rectangles.",
        H("EmptyRowFilling"), Blocks(
            Paragraph(Text("The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.")),
            Describe.Lean(DescribeId.Create("empty-row-filling-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.FirstEmptyFibre"), H("FirstEmptyFibre"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("empty-row-filling-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.firstEmptyFibre_card"), H("firstEmptyFibre_card"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("empty-row-filling-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFilling.S_col"), H("S_col"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Proposition 4.3 (p. 8), obtained by filling the first empty row and choosing the remaining nonempty rows."))), DescribeRole.Lemma)), []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hkr"), Sp, Colon, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Named("FirstEmptyFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Named("hkr"), Sp, Colon, Sp, Named("Type")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hkr"), Sp, Colon, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Named("FirstEmptyFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Named("hkr"), Sp, Eq, Sp, Parenthesized(new Formula.SetLiteral([Seq(F.Id("R"), Sp, Colon, Sp, Named("Counted"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("k"), Sp, Bar, Sp, Parenthesized(Seq(Forall, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("R"), Sp, Dot, Sp, Named("val"), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Named("val")), Rangle), Sp, F.Id("c"), Sp, Eq, Sp, D(0))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("i"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("r"), Sp, Comma, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"), Sp, Lt, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, To, Sp, Exists, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("R"), Sp, Dot, Sp, Named("val"), Sp, F.Id("i"), Sp, F.Id("c"), Sp, Neq, Sp, D(0))))])))]));

    private static Formula Formula1() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hkr"), Sp, Colon, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("FirstEmptyFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Named("hkr"))), Sp, Eq, Sp, F.Id("S"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Cdot, Sp, Named("Nat"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val")))));

    private static Formula Formula2() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("k"))), Sp, To, Sp, Parenthesized(Seq(F.Id("k"), Sp, Lt, Sp, F.Id("r"))), Sp, To, Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Eq, Sp, new Formula.Subscript(Sum, Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z")))))));
}

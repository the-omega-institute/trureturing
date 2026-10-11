using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AlternatingSignRectangles;

internal sealed class InteriorRecurrenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hongesberg2026asr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "InteriorRecurrence for extendably 312-avoiding alternating sign rectangles.",
        H("InteriorRecurrence"), Blocks(
            Paragraph(Text("The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.")),
            Describe.Lean(DescribeId.Create("interior-recurrence-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/InteriorRecurrence.S_interior"), H("S_interior"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 4.4 (pp. 8–9), combining the first-column and first-empty-row decompositions."))), DescribeRole.Lemma)), []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("d"))), Sp, To, Sp, Parenthesized(Seq(F.Id("d"), Sp, Lt, Sp, F.Id("r"))), Sp, To, Sp, Parenthesized(Seq(F.Id("d"), Sp, Lt, Sp, F.Id("k"))), Sp, To, Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Eq, Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("r"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Plus, Sp, Parenthesized(Seq(F.Id("S"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, D(1))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Plus, Sp, new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, Seq(Named("CoeSort"), Dot, Named("coe")), Sp, Parenthesized(Seq(Named("Icc"), Sp, D(2), Sp, F.Id("d"))))), Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(2))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("S"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z")))))))));
}

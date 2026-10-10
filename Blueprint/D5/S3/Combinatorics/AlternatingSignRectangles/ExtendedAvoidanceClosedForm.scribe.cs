using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AlternatingSignRectangles;

internal sealed class ExtendedAvoidanceClosedFormDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hongesberg2026asr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ExtendedAvoidanceClosedForm for extendably 312-avoiding alternating sign rectangles.",
        H("ExtendedAvoidanceClosedForm"), Blocks(
            Paragraph(Text("The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.")),
            Describe.Lean(DescribeId.Create("extended-avoidance-closed-form-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.F"), H("F"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (4.2), p. 9. All subtraction between natural numbers is truncated subtraction; subtraction between integers is integer subtraction. binom uses Ring.choose and vanishes for a negative lower index."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extended-avoidance-closed-form-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.claim"), H("claim"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source states verbatim: “Conjecture 4.5. For integers d ≤ r, k, we have” (p. 9), followed by equation (4.2). The parameters r, k, d range over ℕ, and the literal count is coerced to ℤ."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extended-avoidance-closed-form-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.result"), H("result"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The closed form follows from the three source recurrences, the large-Schröder power series, the diagonal coefficient identity, and the even-Catalan identity."))), DescribeRole.Theorem)), []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("F"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z")))), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("F"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, InMacro, Sp, Named("Icc"), Sp, D(1), Sp, F.Id("d"))), Sp, Parenthesized(Seq(D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Seq(Caret, Grp(Parenthesized(Seq(F.Id("i"), Sp, Minus, Sp, D(1))))), Sp, Cdot, Sp, Named("Ring"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, F.Id("i"), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Named("if"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, F.Id("i"))), Sp, Lt, Sp, D(0), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Named("Ring"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, D(2))), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, F.Id("i"))), Sp, Dot, Sp, Named("toNat"))), Sp, Minus, Sp, D(2), Sp, Cdot, Sp, Parenthesized(Seq(Named("if"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, F.Id("i"), Sp, Minus, Sp, D(2))), Sp, Lt, Sp, D(0), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Named("Ring"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, D(2))), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, F.Id("i"), Sp, Minus, Sp, D(2))), Sp, Dot, Sp, Named("toNat"))))))), Sp, Plus, Sp, Named("Ring"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, F.Id("d"), Sp, Plus, Sp, Parenthesized(Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, InMacro, Sp, Named("range"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Parenthesized(Seq(Named("catalan"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("i"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, Parenthesized(Seq(Named("if"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, D(1), Sp, Minus, Sp, D(2), Sp, Cdot, Sp, F.Id("i"))), Sp, Lt, Sp, D(0), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Named("Ring"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, D(1), Sp, Plus, Sp, D(2), Sp, Cdot, Sp, F.Id("i"))), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp, D(1), Sp, Minus, Sp, D(2), Sp, Cdot, Sp, F.Id("i"))), Sp, Dot, Sp, Named("toNat"))))), Sp, Plus, Sp, D(2), Sp, Cdot, Sp, new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, InMacro, Sp, Named("Icc"), Sp, D(1), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Minus, Sp, D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Seq(Caret, Grp(F.Id("i"))), Sp, Cdot, Sp, Named("Ring"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, F.Id("i"))))))]));

    private static Formula Formula1() =>
        Disp(new Formula.Aligned([Seq(Named("claim"), Sp, Colon, Sp, Named("Prop")), Seq(Named("claim"), Sp, Leftrightarrow, Sp, Parenthesized(Seq(Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, F.Id("d"), Sp, Le, Sp, F.Id("r"), Sp, To, Sp, F.Id("d"), Sp, Le, Sp, F.Id("k"), Sp, To, Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Eq, Sp, F.Id("F"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"))))]));

    private static Formula Formula2() =>
        Disp(Seq(Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, F.Id("d"), Sp, Le, Sp, F.Id("r"), Sp, To, Sp, F.Id("d"), Sp, Le, Sp, F.Id("k"), Sp, To, Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Eq, Sp, F.Id("F"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d")));
}

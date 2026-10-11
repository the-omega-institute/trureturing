using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AlternatingSignRectangles;

internal sealed class SquareMergeConstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hongesberg2026asr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SquareMergeConstruction for extendably 312-avoiding alternating sign rectangles.",
        H("SquareMergeConstruction"), Blocks(
            Paragraph(Text("The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.")),
            Describe.Lean(DescribeId.Create("square-merge-construction-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.lowerIndex"), H("lowerIndex"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The dependent conditional binds hc as the branch proof of p ≤ c.val. The placeholder in lowerIndex u suppresses its certified proof argument; lowerIndex c hc retains the branch proof."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-merge-construction-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.decCorner"), H("decCorner"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-merge-construction-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner"), H("incCorner"),
                StatementSource.FromAuthor(Formula3()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-merge-construction-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner_dec"), H("incCorner_dec"),
                StatementSource.FromAuthor(Formula4()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.decCorner_inc"), H("decCorner_inc"),
                StatementSource.FromAuthor(Formula5()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-6"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.incCorner_cast"), H("incCorner_cast"),
                StatementSource.FromAuthor(Formula6()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-7"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect"), H("mergeRect"),
                StatementSource.FromAuthor(Formula7()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-merge-construction-8"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_top"), H("mergeRect_top"),
                StatementSource.FromAuthor(Formula8()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The placeholder in shiftCol suppresses the certified width inequality p + 1 ≤ p + k."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-9"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_first_col"), H("mergeRect_first_col"),
                StatementSource.FromAuthor(Formula9()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-10"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_lower"), H("mergeRect_lower"),
                StatementSource.FromAuthor(Formula10()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-11"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_isASR"), H("mergeRect_isASR"),
                StatementSource.FromAuthor(Formula11()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-12"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_extAvoids"), H("mergeRect_extAvoids"),
                StatementSource.FromAuthor(Formula12()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-13"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.mergeRect_nonemptyRows"), H("mergeRect_nonemptyRows"),
                StatementSource.FromAuthor(Formula13()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-14"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.all_rows_nonempty_iff"), H("all_rows_nonempty_iff"),
                StatementSource.FromAuthor(Formula14()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-15"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.asm_nonemptyRows"), H("asm_nonemptyRows"),
                StatementSource.FromAuthor(Formula15()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-merge-construction-16"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareMergeConstruction.square_count_isASM"), H("square_count_isASM"),
                StatementSource.FromAuthor(Formula16()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma)), []));

    private static Formula Call(string name, Formula value) => Seq(Named(name), Sp, value);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, F.Id("n"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hx"), Sp, Colon, Sp, F.Id("p"), Sp, Le, Sp, F.Id("x"), Sp, Dot, Sp, Named("val"))), Sp, Comma, Sp, Named("lowerIndex"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Seq(Colon, Eq), Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("n"), Sp, Seq(Colon, Eq), Sp, F.Id("n"))), Sp, F.Id("x"), Sp, Named("hx"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, F.Id("n"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hx"), Sp, Colon, Sp, F.Id("p"), Sp, Le, Sp, F.Id("x"), Sp, Dot, Sp, Named("val"))), Sp, Comma, Sp, Named("lowerIndex"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Seq(Colon, Eq), Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("n"), Sp, Seq(Colon, Eq), Sp, F.Id("n"))), Sp, F.Id("x"), Sp, Named("hx"), Sp, Eq, Sp, Parenthesized(Seq(Langle, Sp, Seq(F.Id("x"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, F.Id("p")), Rangle)))]));

    private static Formula Formula2() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Named("SignType"))), Sp, Comma, Sp, Named("decCorner"), Sp, F.Id("s"), Sp, Colon, Sp, Named("SignType")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Named("SignType"))), Sp, Comma, Sp, Named("decCorner"), Sp, F.Id("s"), Sp, Eq, Sp, Parenthesized(Seq(Named("if"), Sp, F.Id("s"), Sp, Eq, Sp, D(1), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Minus, Sp, D(1))))]));

    private static Formula Formula3() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Named("SignType"))), Sp, Comma, Sp, Named("incCorner"), Sp, F.Id("s"), Sp, Colon, Sp, Named("SignType")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Named("SignType"))), Sp, Comma, Sp, Named("incCorner"), Sp, F.Id("s"), Sp, Eq, Sp, Parenthesized(Seq(Named("if"), Sp, F.Id("s"), Sp, Eq, Sp, Minus, Sp, D(1), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, D(1))))]));

    private static Formula Formula4() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("s"), Sp, Neq, Sp, Minus, Sp, D(1))), Sp, To, Sp, Named("incCorner"), Sp, Parenthesized(Seq(Named("decCorner"), Sp, F.Id("s"))), Sp, Eq, Sp, F.Id("s")));

    private static Formula Formula5() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("s"), Sp, Neq, Sp, D(1))), Sp, To, Sp, Named("decCorner"), Sp, Parenthesized(Seq(Named("incCorner"), Sp, F.Id("s"))), Sp, Eq, Sp, F.Id("s")));

    private static Formula Formula6() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("s"), Sp, Neq, Sp, D(1))), Sp, To, Sp, Parenthesized(Seq(Named("incCorner"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Eq, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Plus, Sp, D(1)));

    private static Formula Formula7() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Named("mergeRect"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Seq(Colon, Eq), Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Seq(Colon, Eq), Sp, F.Id("r"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Seq(Colon, Eq), Sp, F.Id("k"))), Sp, F.Id("M"), Sp, F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, F.Id("r"))))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, F.Id("k"))))), Sp, Named("SignType")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Named("mergeRect"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Seq(Colon, Eq), Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Seq(Colon, Eq), Sp, F.Id("r"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Seq(Colon, Eq), Sp, F.Id("k"))), Sp, F.Id("M"), Sp, F.Id("B"), Sp, Eq, Sp, Parenthesized(Seq(Named("fun"), Sp, F.Id("u"), Sp, F.Id("c"), Sp, Mapsto, Sp, Named("if"), Sp, F.Id("u"), Sp, Dot, Sp, Named("val"), Sp, Lt, Sp, F.Id("p"), Sp, Named("then"), Sp, Named("if"), Sp, D(0), Sp, Lt, Sp, F.Id("c"), Sp, Dot, Sp, Named("val"), Sp, Land, Sp, F.Id("c"), Sp, Dot, Sp, Named("val"), Sp, Le, Sp, F.Id("p"), Sp, Named("then"), Sp, F.Id("M"), Sp, Seq(Langle, Sp, Seq(F.Id("u"), Sp, Dot, Sp, Named("val")), Rangle), Sp, Seq(Langle, Sp, Seq(F.Id("c"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(1)), Rangle), Sp, Named("else"), Sp, D(0), Sp, Named("else"), Sp, Named("if"), Sp, F.Id("c"), Sp, Dot, Sp, Named("val"), Sp, Eq, Sp, D(0), Sp, Named("then"), Sp, Named("if"), Sp, F.Id("u"), Sp, Dot, Sp, Named("val"), Sp, Eq, Sp, F.Id("p"), Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0), Sp, Named("else"), Sp, Named("if"), Sp, Named("hc"), Sp, Colon, Sp, F.Id("p"), Sp, Le, Sp, Call("val", F.Id("c")), Sp, Named("then"), Sp, Named("if"), Sp, F.Id("u"), Sp, Dot, Sp, Named("val"), Sp, Eq, Sp, F.Id("p"), Sp, Land, Sp, F.Id("c"), Sp, Dot, Sp, Named("val"), Sp, Eq, Sp, F.Id("p"), Sp, Named("then"), Sp, Named("decCorner"), Sp, Parenthesized(Seq(F.Id("B"), Sp, Parenthesized(Seq(Named("lowerIndex"), Sp, F.Id("u"), Sp, new Formula.Placeholder())), Sp, Parenthesized(Seq(Named("lowerIndex"), Sp, F.Id("c"), Sp, Named("hc"))))), Sp, Named("else"), Sp, F.Id("B"), Sp, Parenthesized(Seq(Named("lowerIndex"), Sp, F.Id("u"), Sp, new Formula.Placeholder())), Sp, Parenthesized(Seq(Named("lowerIndex"), Sp, F.Id("c"), Sp, Named("hc"))), Sp, Named("else"), Sp, D(0))))]));

    private static Formula Formula8() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hk"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("k"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, F.Id("c"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("p"))), Sp, Comma, Sp, Named("mergeRect"), Sp, F.Id("M"), Sp, F.Id("B"), Sp, Parenthesized(Seq(F.Id("u"), Sp, Dot, Sp, Named("castAdd"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("shiftCol"), Sp, new Formula.Placeholder(), Sp, F.Id("c"))), Sp, Eq, Sp, F.Id("M"), Sp, F.Id("u"), Sp, F.Id("c")));

    private static Formula Formula9() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("k"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, F.Id("r"))))), Sp, Comma, Sp, Named("mergeRect"), Sp, F.Id("M"), Sp, F.Id("B"), Sp, F.Id("u"), Sp, Seq(Langle, Sp, D(0), Rangle), Sp, Eq, Sp, Named("if"), Sp, F.Id("u"), Sp, Dot, Sp, Named("val"), Sp, Eq, Sp, F.Id("p"), Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0)));

    private static Formula Formula10() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("p"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("r"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("c"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("k"))), Sp, Comma, Sp, Named("mergeRect"), Sp, F.Id("M"), Sp, F.Id("B"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Dot, Sp, Named("natAdd"), Sp, F.Id("p"), Sp, F.Id("u"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Dot, Sp, Named("natAdd"), Sp, F.Id("p"), Sp, F.Id("c"))), Sp, Eq, Sp, Named("if"), Sp, F.Id("u"), Sp, Dot, Sp, Named("val"), Sp, Eq, Sp, D(0), Sp, Land, Sp, F.Id("c"), Sp, Dot, Sp, Named("val"), Sp, Eq, Sp, D(0), Sp, Named("then"), Sp, Named("decCorner"), Sp, Parenthesized(Seq(F.Id("B"), Sp, F.Id("u"), Sp, F.Id("c"))), Sp, Named("else"), Sp, F.Id("B"), Sp, F.Id("u"), Sp, F.Id("c")));

    private static Formula Formula11() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("p"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("k"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(Named("IsASM"), Sp, F.Id("M"))), Sp, To, Sp, Parenthesized(Seq(Named("IsASR"), Sp, F.Id("B"))), Sp, To, Sp, Parenthesized(Seq(Exists, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("B"), Sp, Seq(Langle, Sp, Seq(D(0), Sp, Comma, Sp, Named("hr")), Rangle), Sp, F.Id("c"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Named("IsASR"), Sp, Parenthesized(Seq(Named("mergeRect"), Sp, F.Id("M"), Sp, F.Id("B")))));

    private static Formula Formula12() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("p"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("k"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(Named("IsASM"), Sp, F.Id("M"))), Sp, To, Sp, Parenthesized(Seq(Neg, Sp, Named("Contains312"), Sp, F.Id("M"))), Sp, To, Sp, Parenthesized(Seq(Named("IsASR"), Sp, F.Id("B"))), Sp, To, Sp, Parenthesized(Seq(Named("ExtAvoids312"), Sp, F.Id("B"))), Sp, To, Sp, Parenthesized(Seq(Exists, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("B"), Sp, Seq(Langle, Sp, Seq(D(0), Sp, Comma, Sp, Named("hr")), Rangle), Sp, F.Id("c"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Named("ExtAvoids312"), Sp, Parenthesized(Seq(Named("mergeRect"), Sp, F.Id("M"), Sp, F.Id("B")))));

    private static Formula Formula13() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("p"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("k"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("p"))), Sp, Named("SignType"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(Named("IsASM"), Sp, F.Id("M"))), Sp, To, Sp, Parenthesized(Seq(Named("IsASR"), Sp, F.Id("B"))), Sp, To, Sp, Parenthesized(Seq(Exists, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("B"), Sp, Seq(Langle, Sp, Seq(D(0), Sp, Comma, Sp, Named("hr")), Rangle), Sp, F.Id("c"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Named("nonemptyRows"), Sp, Parenthesized(Seq(Named("mergeRect"), Sp, F.Id("M"), Sp, F.Id("B"))), Sp, Eq, Sp, F.Id("p"), Sp, Plus, Sp, Named("nonemptyRows"), Sp, F.Id("B")));

    private static Formula Formula14() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"))), Sp, Comma, Sp, Named("nonemptyRows"), Sp, F.Id("R"), Sp, Eq, Sp, F.Id("r"), Sp, Leftrightarrow, Sp, Forall, Sp, F.Id("u"), Sp, Comma, Sp, Exists, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("R"), Sp, F.Id("u"), Sp, F.Id("c"), Sp, Neq, Sp, D(0)));

    private static Formula Formula15() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(Named("IsASM"), Sp, F.Id("M"))), Sp, To, Sp, Named("nonemptyRows"), Sp, F.Id("M"), Sp, Eq, Sp, F.Id("n")));

    private static Formula Formula16() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Named("SignType"))), Sp, Comma, Sp, Parenthesized(Seq(Named("IsASR"), Sp, F.Id("M"))), Sp, To, Sp, Parenthesized(Seq(Named("nonemptyRows"), Sp, F.Id("M"), Sp, Eq, Sp, F.Id("n"))), Sp, To, Sp, Named("IsASM"), Sp, F.Id("M")));
}

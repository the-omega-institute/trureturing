using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AlternatingSignRectangles;

internal sealed class SquareFirstColumnDecompositionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hongesberg2026asr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SquareFirstColumnDecomposition for extendably 312-avoiding alternating sign rectangles.",
        H("SquareFirstColumnDecomposition"), Blocks(
            Paragraph(Text("The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.")),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.AvoidASM"), H("AvoidASM"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.FirstNonempty"), H("FirstNonempty"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.ColumnFibre"), H("ColumnFibre"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.mergeColumnFibre"), H("mergeColumnFibre"),
                StatementSource.FromAuthor(Formula3()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed entries specify the certified merge, with Fin value-preserving dimension casts and subtype proof fields suppressed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.firstColumnFactor_card"), H("firstColumnFactor_card"),
                StatementSource.FromAuthor(Formula4()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.squareCount_card"), H("squareCount_card"),
                StatementSource.FromAuthor(Formula5()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-6"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.AvoidASM_zero_card"), H("AvoidASM_zero_card"),
                StatementSource.FromAuthor(Formula6()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-7"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asm_extAvoids"), H("asm_extAvoids"),
                StatementSource.FromAuthor(Formula7()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-8"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asm_first_column_one"), H("asm_first_column_one"),
                StatementSource.FromAuthor(Formula8()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-9"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.ASMFibre"), H("ASMFibre"),
                StatementSource.FromAuthor(Formula9()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-10"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.fullFirstNonemptyEquiv"), H("fullFirstNonemptyEquiv"),
                StatementSource.FromAuthor(Formula10()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted. The two equalities give the toFun and invFun fields; subtype proof fields are suppressed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-first-column-decomposition-11"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/SquareFirstColumnDecomposition.asmNonzeroFibre_card"), H("asmNonzeroFibre_card"),
                StatementSource.FromAuthor(Formula11()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma)), []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("AvoidASM"), Sp, F.Id("n"), Sp, Colon, Sp, Named("Type")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("AvoidASM"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(new Formula.SetLiteral([Seq(F.Id("M"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("n"))), Sp, Named("SignType"), Sp, Bar, Sp, Named("IsASM"), Sp, F.Id("M"), Sp, Land, Sp, Neg, Sp, Named("Contains312"), Sp, F.Id("M"))])))]));

    private static Formula Formula1() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Named("FirstNonempty"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Named("hr"), Sp, Colon, Sp, Named("Type")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Named("FirstNonempty"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Named("hr"), Sp, Eq, Sp, Parenthesized(new Formula.SetLiteral([Seq(F.Id("B"), Sp, Colon, Sp, Named("Counted"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Bar, Sp, Exists, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("B"), Sp, Dot, Sp, Named("val"), Sp, Seq(Langle, Sp, D(0), Rangle), Sp, F.Id("c"), Sp, Neq, Sp, D(0))])))]));

    private static Formula Formula2() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hk"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("k"))), Sp, Comma, Sp, Named("ColumnFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Named("hr"), Sp, Named("hk"), Sp, Colon, Sp, Named("Type")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hk"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("k"))), Sp, Comma, Sp, Named("ColumnFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Named("hr"), Sp, Named("hk"), Sp, Eq, Sp, Parenthesized(new Formula.SetLiteral([Seq(F.Id("R"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(Named("Fin"), Sp, F.Id("k"))), Sp, Named("SignType"), Sp, Bar, Sp, Named("IsASR"), Sp, F.Id("R"), Sp, Land, Sp, Named("ExtAvoids312"), Sp, F.Id("R"), Sp, Land, Sp, Named("nonemptyRows"), Sp, F.Id("R"), Sp, Eq, Sp, F.Id("d"), Sp, Land, Sp, F.Id("R"), Sp, Seq(Langle, Sp, F.Id("p"), Rangle), Sp, Seq(Langle, Sp, D(0), Rangle), Sp, Eq, Sp, D(1), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("r"), Sp, Comma, Sp, F.Id("v"), Sp, Dot, Sp, Named("val"), Sp, Lt, Sp, F.Id("p"), Sp, To, Sp, Exists, Sp, F.Id("c"), Sp, Comma, Sp, F.Id("R"), Sp, F.Id("v"), Sp, F.Id("c"), Sp, Neq, Sp, D(0))))])))]));

    private static Formula Formula3() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hk"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("k"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hp"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("p"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hd"), Sp, Colon, Sp, F.Id("p"), Sp, Le, Sp, F.Id("d"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("AvoidASM"), Sp, F.Id("p"), Sp, Times, Sp, Named("FirstNonempty"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, F.Id("p"))), Sp, new Formula.Placeholder())), Sp, Comma, Sp, Named("mergeColumnFibre"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Seq(Colon, Eq), Sp, F.Id("r"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Seq(Colon, Eq), Sp, F.Id("k"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Seq(Colon, Eq), Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Seq(Colon, Eq), Sp, F.Id("p"))), Sp, Named("hr"), Sp, Named("hk"), Sp, Named("hp"), Sp, Named("hd"), Sp, F.Id("x"), Sp, Colon, Sp, Named("ColumnFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Named("hr"), Sp, Named("hk")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hk"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("k"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hp"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("p"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hd"), Sp, Colon, Sp, F.Id("p"), Sp, Le, Sp, F.Id("d"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Named("AvoidASM"), Sp, F.Id("p"), Sp, Times, Sp, Named("FirstNonempty"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, F.Id("p"))), Sp, new Formula.Placeholder())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("k"))), Sp, Comma, Sp, Parenthesized(Seq(Named("mergeColumnFibre"), Sp, Named("hr"), Sp, Named("hk"), Sp, Named("hp"), Sp, Named("hd"), Sp, F.Id("x"))), Sp, Dot, Sp, Named("val"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Eq, Sp, Named("mergeRect"), Sp, F.Id("x"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, Named("val"), Sp, F.Id("x"), Sp, Dot, Sp, D(2), Sp, Dot, Sp, Named("val"), Sp, Dot, Sp, Named("val"), Sp, Seq(Langle, Sp, Seq(F.Id("i"), Sp, Dot, Sp, Named("val")), Rangle), Sp, Seq(Langle, Sp, Seq(F.Id("j"), Sp, Dot, Sp, Named("val")), Rangle))]));

    private static Formula Formula4() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hk"), Sp, Colon, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("k"))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("p"))), Sp, To, Sp, Parenthesized(Seq(F.Id("p"), Sp, Le, Sp, F.Id("d"))), Sp, To, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("ColumnFibre"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, F.Id("p"), Sp, Named("hr"), Sp, Named("hk"))), Sp, Eq, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("AvoidASM"), Sp, F.Id("p"))), Sp, Cdot, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("FirstNonempty"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, F.Id("p"))), Sp, new Formula.Placeholder()))));

    private static Formula Formula5() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("S"), Sp, F.Id("n"), Sp, F.Id("n"), Sp, F.Id("n"), Sp, Eq, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("AvoidASM"), Sp, F.Id("n")))));

    private static Formula Formula6() =>
        Disp(Seq(Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("AvoidASM"), Sp, D(0))), Sp, Eq, Sp, D(1)));

    private static Formula Formula7() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("AvoidASM"), Sp, F.Id("n"))), Sp, Comma, Sp, Named("ExtAvoids312"), Sp, F.Id("M"), Sp, Dot, Sp, Named("val")));

    private static Formula Formula8() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Named("AvoidASM"), Sp, F.Id("n"))), Sp, Comma, Sp, Exists, Sp, F.Id("u"), Sp, Comma, Sp, F.Id("M"), Sp, Dot, Sp, Named("val"), Sp, F.Id("u"), Sp, Seq(Langle, Sp, D(0), Rangle), Sp, Eq, Sp, D(1)));

    private static Formula Formula9() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hn"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Named("ASMFibre"), Sp, F.Id("n"), Sp, Named("hn"), Sp, F.Id("p"), Sp, Colon, Sp, Named("Type")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hn"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Named("ASMFibre"), Sp, F.Id("n"), Sp, Named("hn"), Sp, F.Id("p"), Sp, Eq, Sp, Parenthesized(new Formula.SetLiteral([Seq(F.Id("M"), Sp, Colon, Sp, Named("AvoidASM"), Sp, F.Id("n"), Sp, Bar, Sp, F.Id("M"), Sp, Dot, Sp, Named("val"), Sp, F.Id("p"), Sp, Seq(Langle, Sp, D(0), Rangle), Sp, Eq, Sp, D(1))])))]));

    private static Formula Formula10() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Named("fullFirstNonemptyEquiv"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Named("hr"), Sp, Colon, Sp, Named("Equiv"), Sp, Parenthesized(Seq(Named("FirstNonempty"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("r"), Sp, Named("hr"))), Sp, Parenthesized(Seq(Named("Counted"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("r")))), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hr"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("r"))), Sp, Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Named("fullFirstNonemptyEquiv"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Named("hr"))), Sp, Dot, Sp, Named("toFun"), Sp, Eq, Sp, Parenthesized(Seq(Named("fun"), Sp, F.Id("B"), Sp, Mapsto, Sp, F.Id("B"), Sp, Dot, Sp, Named("val"))))), Sp, Land, Sp, Parenthesized(Seq(Parenthesized(Seq(Named("fullFirstNonemptyEquiv"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, Named("hr"))), Sp, Dot, Sp, Named("invFun"), Sp, Eq, Sp, Parenthesized(Seq(Named("fun"), Sp, F.Id("B"), Sp, Mapsto, Sp, Seq(Langle, Sp, F.Id("B"), Rangle))))))]));

    private static Formula Formula11() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Named("hn"), Sp, Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Named("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("p"), Sp, Dot, Sp, Named("val"))), Sp, To, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("ASMFibre"), Sp, F.Id("n"), Sp, Named("hn"), Sp, F.Id("p"))), Sp, Eq, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("AvoidASM"), Sp, F.Id("p"), Sp, Dot, Sp, Named("val"))), Sp, Cdot, Sp, Named("Nat"), Sp, Dot, Sp, Named("card"), Sp, Parenthesized(Seq(Named("AvoidASM"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Minus, Sp, F.Id("p"), Sp, Dot, Sp, Named("val")))))));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AlternatingSignRectangles;

internal sealed class RecurrenceSeriesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hongesberg2026asr");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RecurrenceSeries for extendably 312-avoiding alternating sign rectangles.",
        H("RecurrenceSeries"), Blocks(
            Paragraph(Text("The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.")),
            Describe.Lean(DescribeId.Create("recurrence-series-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.T"), H("T"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.RecurrenceSpec"), H("RecurrenceSpec"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.recurrence_unique"), H("recurrence_unique"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("recurrence-series-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.q"), H("q"),
                StatementSource.FromAuthor(Formula4()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.A"), H("A"),
                StatementSource.FromAuthor(Formula5()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-6"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.U"), H("U"),
                StatementSource.FromAuthor(Formula6()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-7"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.V"), H("V"),
                StatementSource.FromAuthor(Formula7()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-8"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.G"), H("G"),
                StatementSource.FromAuthor(Formula8()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-9"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.q_constant"), H("q_constant"),
                StatementSource.FromAuthor(Formula9()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-10"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.U_left"), H("U_left"),
                StatementSource.FromAuthor(Formula10()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-11"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.V_left"), H("V_left"),
                StatementSource.FromAuthor(Formula11()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-12"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.R_as_q"), H("R_as_q"),
                StatementSource.FromAuthor(Formula12()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-13"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.half_cancel"), H("half_cancel"),
                StatementSource.FromAuthor(Formula13()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-14"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.transform"), H("transform"),
                StatementSource.FromAuthor(Formula14()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-15"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.transform_eq"), H("transform_eq"),
                StatementSource.FromAuthor(Formula15()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-17"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.z"), H("z"),
                StatementSource.FromAuthor(Formula17()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-18"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.z_constant"), H("z_constant"),
                StatementSource.FromAuthor(Formula18()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-19"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.even_Catalan_identity"), H("even_Catalan_identity"),
                StatementSource.FromAuthor(Formula19()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-20"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.finite_mul_subst"), H("finite_mul_subst"),
                StatementSource.FromAuthor(Formula20()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-21"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.mul_pow_vanish"), H("mul_pow_vanish"),
                StatementSource.FromAuthor(Formula21()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-22"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.even_sum_reindex"), H("even_sum_reindex"),
                StatementSource.FromAuthor(Formula22()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-23"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.Cnt"), H("Cnt"),
                StatementSource.FromAuthor(Formula23()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The displayed equality gives the defining mathematical data; Prop-valued constructor fields are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence-series-24"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.Cnt_admissible"), H("Cnt_admissible"),
                StatementSource.FromAuthor(Formula24()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("recurrence-series-25"),
                DeclarationHandle.Create("D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries.series_eq_T"), H("series_eq_T"),
                StatementSource.FromAuthor(Formula25()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The implication holds for every parameter and sign matrix in the stated domains."))), DescribeRole.Lemma)), []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z")))), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(Named("if"), Sp, F.Id("r"), Sp, Lt, Sp, F.Id("d"), Sp, Lor, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("d"), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Named("if"), Sp, F.Id("d"), Sp, Eq, Sp, D(0), Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, Named("if"), Sp, F.Id("r"), Sp, Eq, Sp, F.Id("d"), Sp, Land, Sp, F.Id("k"), Sp, Eq, Sp, F.Id("d"), Sp, Named("then"), Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, D(1))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Named("else"), Sp, Named("if"), Sp, F.Id("d"), Sp, Eq, Sp, F.Id("r"), Sp, Named("then"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, F.Id("d"), Sp, Plus, Sp, F.Id("T"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, D(1))), Sp, Plus, Sp, new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, Seq(Named("CoeSort"), Dot, Named("coe")), Sp, Parenthesized(Seq(Named("Icc"), Sp, D(2), Sp, F.Id("d"))))), Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(2))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, F.Id("T"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Named("else"), Sp, Named("if"), Sp, F.Id("d"), Sp, Eq, Sp, F.Id("k"), Sp, Named("then"), Sp, new Formula.Subscript(Sum, Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, F.Id("T"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Cdot, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Named("else"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, F.Id("d"), Sp, Plus, Sp, F.Id("T"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, D(1))), Sp, Plus, Sp, new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, Seq(Named("CoeSort"), Dot, Named("coe")), Sp, Parenthesized(Seq(Named("Icc"), Sp, D(2), Sp, F.Id("d"))))), Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(2))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("T"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Minus, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))))))))]));

    private static Formula Formula1() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Named("RecurrenceSpec"), Sp, F.Id("f"), Sp, Colon, Sp, Named("Prop")), Seq(Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Named("RecurrenceSpec"), Sp, F.Id("f"), Sp, Leftrightarrow, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Comma, Sp, F.Id("r"), Sp, Lt, Sp, F.Id("d"), Sp, Lor, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("d"), Sp, To, Sp, F.Id("f"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, D(0))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("f"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, D(0), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("d"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, F.Id("d"), Sp, To, Sp, F.Id("f"), Sp, F.Id("d"), Sp, F.Id("d"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, D(1))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, F.Id("r"), Sp, To, Sp, F.Id("r"), Sp, Lt, Sp, F.Id("k"), Sp, To, Sp, F.Id("f"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("r"), Sp, Eq, Sp, F.Id("f"), Sp, F.Id("r"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, F.Id("r"), Sp, Plus, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, D(1))), Sp, Plus, Sp, new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, Seq(Named("CoeSort"), Dot, Named("coe")), Sp, Parenthesized(Seq(Named("Icc"), Sp, D(2), Sp, F.Id("r"))))), Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(2))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, F.Id("k"), Sp, To, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("r"), Sp, To, Sp, F.Id("f"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("k"), Sp, Eq, Sp, new Formula.Subscript(Sum, Seq(F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, F.Id("f"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, F.Id("k"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Cdot, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("j"), Sp, Dot, Sp, Named("val"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, F.Id("d"), Sp, To, Sp, F.Id("d"), Sp, Lt, Sp, F.Id("r"), Sp, To, Sp, F.Id("d"), Sp, Lt, Sp, F.Id("k"), Sp, To, Sp, F.Id("f"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, F.Id("f"), Sp, F.Id("r"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, F.Id("d"), Sp, Plus, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Minus, Sp, D(1))), Sp, Plus, Sp, new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, Seq(Named("CoeSort"), Dot, Named("coe")), Sp, Parenthesized(Seq(Named("Icc"), Sp, D(2), Sp, F.Id("d"))))), Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("largeSchroder"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Dot, Sp, Named("val"), Sp, Minus, Sp, D(2))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("f"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Minus, Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("choose"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, F.Id("i"), Sp, Dot, Sp, Named("val"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))))))))))]));

    private static Formula Formula2() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Parenthesized(Seq(Named("RecurrenceSpec"), Sp, F.Id("f"))), Sp, To, Sp, Forall, Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Comma, Sp, F.Id("f"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d")));

    private static Formula Formula4() =>
        Disp(new Formula.Aligned([Seq(F.Id("q"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))), Seq(F.Id("q"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("X"), Sp, Cdot, Sp, F.Id("R"))))]));

    private static Formula Formula5() =>
        Disp(new Formula.Aligned([Seq(F.Id("A"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))), Seq(F.Id("A"), Sp, Eq, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, F.Id("q"))))]));

    private static Formula Formula6() =>
        Disp(new Formula.Aligned([Seq(F.Id("U"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))), Seq(F.Id("U"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Minus, Sp, F.Id("q"))), Sp, Seq(Caret, Grp(Minus, D(1))))))]));

    private static Formula Formula7() =>
        Disp(new Formula.Aligned([Seq(F.Id("V"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))), Seq(F.Id("V"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Minus, Sp, F.Id("X"))), Sp, Seq(Caret, Grp(Minus, D(1))))))]));

    private static Formula Formula8() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("G"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))), Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("G"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("C"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Cdot, Sp, F.Id("A"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("R"), Sp, Seq(Caret, Grp(F.Id("b"))), Sp, Cdot, Sp, F.Id("U"), Sp, Seq(Caret, Grp(F.Id("a"))), Sp, Plus, Sp, F.Id("V"), Sp, Seq(Caret, Grp(F.Id("a"))))))))]));

    private static Formula Formula9() =>
        Disp(Seq(Named("constantCoeff"), Sp, F.Id("q"), Sp, Eq, Sp, D(0)));

    private static Formula Formula10() =>
        Disp(Seq(F.Id("U"), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, F.Id("q"))), Sp, Eq, Sp, D(1)));

    private static Formula Formula11() =>
        Disp(Seq(F.Id("V"), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, Parenthesized(Seq(F.Id("X"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))))), Sp, Eq, Sp, D(1)));

    private static Formula Formula12() =>
        Disp(Seq(F.Id("R"), Sp, Eq, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, F.Id("q"))), Sp, Cdot, Sp, F.Id("U")));

    private static Formula Formula13() =>
        Disp(Seq(Parenthesized(Seq(D(2), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Cdot, Sp, F.Id("C"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, D(1)));

    private static Formula Formula14() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, F.Id("Q"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Comma, Sp, Named("transform"), Sp, F.Id("B"), Sp, F.Id("Q"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))), Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, F.Id("Q"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Comma, Sp, Named("transform"), Sp, F.Id("B"), Sp, F.Id("Q"), Sp, Eq, Sp, Parenthesized(Seq(Named("mk"), Sp, Named("fun"), Sp, F.Id("n"), Sp, Mapsto, Sp, Named("coeff"), Sp, F.Id("n"), Sp, Parenthesized(Seq(F.Id("B"), Sp, Cdot, Sp, F.Id("Q"), Sp, Seq(Caret, Grp(F.Id("n"))))))))]));

    private static Formula Formula15() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, F.Id("Q"), Sp, Named("Qinv"), Sp, F.Id("u"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Comma, Sp, Parenthesized(Seq(Named("constantCoeff"), Sp, F.Id("u"), Sp, Eq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("u"), Sp, Eq, Sp, F.Id("X"), Sp, Cdot, Sp, F.Id("Q"), Sp, Dot, Sp, Named("subst"), Sp, F.Id("u"))), Sp, To, Sp, Parenthesized(Seq(Named("Qinv"), Sp, Cdot, Sp, F.Id("Q"), Sp, Eq, Sp, D(1))), Sp, To, Sp, Named("transform"), Sp, F.Id("B"), Sp, F.Id("Q"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("B"), Sp, Cdot, Sp, Named("Qinv"))), Sp, Dot, Sp, Named("subst"), Sp, F.Id("u"), Sp, Cdot, Sp, Named("derivative"), Sp, Seq(Mathbb, Grp(F.Id("Q"))), Sp, F.Id("u")));

    private static Formula Formula17() =>
        Disp(new Formula.Aligned([Seq(F.Id("z"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q")))))), Seq(F.Id("z"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("X"), Sp, Cdot, Sp, F.Id("V"), Sp, Seq(Caret, Grp(D(2))))))]));

    private static Formula Formula18() =>
        Disp(Seq(Named("constantCoeff"), Sp, F.Id("z"), Sp, Eq, Sp, D(0)));

    private static Formula Formula19() =>
        Disp(Seq(D(1), Sp, Plus, Sp, F.Id("z"), Sp, Cdot, Sp, Parenthesized(Seq(Seq(Named("P"), D(1,3), Named("CatalanLagrangeBridge"), Dot, Named("catalanUnit")), Sp, Dot, Sp, Named("subst"), Sp, F.Id("z"), Sp, Plus, Sp, Seq(Named("P"), D(1,3), Named("CatalanLagrangeBridge"), Dot, Named("catalanUnit")), Sp, Dot, Sp, Named("subst"), Sp, Parenthesized(Seq(Minus, Sp, F.Id("z"))))), Sp, Eq, Sp, F.Id("A"), Sp, Cdot, Sp, F.Id("V")));

    private static Formula Formula20() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("u"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Comma, Sp, Parenthesized(Seq(Named("constantCoeff"), Sp, F.Id("u"), Sp, Eq, Sp, D(0))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("coeff"), Sp, F.Id("n"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("B"), Sp, Dot, Sp, Named("subst"), Sp, F.Id("u"))), Sp, Eq, Sp, new Formula.Subscript(Sum, Seq(F.Id("p"), Sp, InMacro, Sp, Named("range"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Named("coeff"), Sp, F.Id("p"), Sp, F.Id("B"), Sp, Cdot, Sp, Named("coeff"), Sp, F.Id("n"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("u"), Sp, Seq(Caret, Grp(F.Id("p")))))));

    private static Formula Formula21() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("u"), Sp, Colon, Sp, Parenthesized(Seq(Named("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Comma, Sp, Parenthesized(Seq(Named("constantCoeff"), Sp, F.Id("u"), Sp, Eq, Sp, D(0))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("n"), Sp, Lt, Sp, F.Id("p"))), Sp, To, Sp, Named("coeff"), Sp, F.Id("n"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("u"), Sp, Seq(Caret, Grp(F.Id("p"))))), Sp, Eq, Sp, D(0)));

    private static Formula Formula22() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Parenthesized(Seq(new Formula.Subscript(Sum, Seq(F.Id("p"), Sp, InMacro, Sp, Named("range"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Named("if"), Sp, Named("Even"), Sp, F.Id("p"), Sp, Named("then"), Sp, F.Id("f"), Sp, F.Id("p"), Sp, Named("else"), Sp, D(0))), Sp, Eq, Sp, new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, InMacro, Sp, Named("range"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Named("if"), Sp, D(2), Sp, Cdot, Sp, F.Id("i"), Sp, Le, Sp, F.Id("n"), Sp, Named("then"), Sp, F.Id("f"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("i"))), Sp, Named("else"), Sp, D(0)));

    private static Formula Formula23() =>
        Disp(new Formula.Aligned([Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("Cnt"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q")))), Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("Cnt"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(Named("if"), Sp, F.Id("r"), Sp, Lt, Sp, F.Id("d"), Sp, Lor, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("d"), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Named("coeff"), Sp, F.Id("d"), Sp, Parenthesized(Seq(F.Id("G"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("d"))))))))]));

    private static Formula Formula24() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("d"), Sp, Le, Sp, F.Id("r"))), Sp, To, Sp, Parenthesized(Seq(F.Id("d"), Sp, Le, Sp, F.Id("k"))), Sp, To, Sp, Named("Cnt"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, Named("coeff"), Sp, F.Id("d"), Sp, Parenthesized(Seq(F.Id("G"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Minus, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Minus, Sp, F.Id("d")))))));

    private static Formula Formula25() =>
        Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("Cnt"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("T"), Sp, F.Id("r"), Sp, F.Id("k"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q")))))));
}

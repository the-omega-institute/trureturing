using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix;
internal sealed class HardinA229532StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229532";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Exact width-six HDA transfer.", H("Width-six transfer data"), Blocks(
            Describe.Lean(DescribeId.Create("between"), DeclarationHandle.Create(Prefix + "between"), H("Both diagonal bond sets"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229532StripData.between"), Call("Finset", Product(Fin(6), Fin(6)))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The bond set is HardinA229584StripData.antidiagonal union its image under Prod.swap. All endpoints lie in Fin 6; no vertical or wrapping bonds are included. The structural zero-cost cut pins its compatibility predicate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"), DeclarationHandle.Create(Prefix + "Valid"), H("Residual-budget invariant"), StatementSource.FromAuthor(Disp(All("p", RowType(), All("d", Call("Nat"), Eq(Call("HardinA229532StripData.Valid", V("p"), V("d")), And(Le(V("d"), Num("1")), Le(Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("p"), V("p")), Sub(Num("1"), V("d"))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The residual budget is at most one and horizontal defects are at most one minus that budget, using truncated natural subtraction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"), H("cl"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229532StripData.cl"), new Formula.TypeArrow(RowType(), new Formula.TypeArrow(Call("Nat"), Fin(31)))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("There are ten proper active classes, ten proper terminal classes, and eleven defective terminal signature classes. Proper classes use HardinA233172DiagonalStrip.boundaryClass minus one, with ten added at zero residual. The equality code on fifteen position pairs selects the other classes. The combined transition_counts theorem pins every class against actual successor rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"), H("T"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229532StripData.T"), Call("Matrix", Fin(31), Fin(31), Call("Int"))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The 31 by 31 integer table retains the frozen saturated proper-colouring transfer in both proper diagonal blocks: entry (i,j) is HardinA233172DiagonalStrip.transfer (i+1) (j+1) divided by 64. The raw_successors theorem accounts for that exact multiplicity. New off-diagonal and defective rows are pinned by the combined transition_counts theorem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"), H("initial"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229532StripData.initial"), new Formula.TypeArrow(Fin(31), Call("Int"))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The thirty-one integer initial weights count each labelled first row with horizontal defects at most one, using residual one minus those defects. The finite_certificate theorem pins the complete row sum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"), H("terminal"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229532StripData.terminal"), new Formula.TypeArrow(Fin(31), Call("Int"))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The first ten entries are zero; all twenty-one remaining entries are one. The finite_certificate theorem pins this to zero residual budget on valid rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"), H("W"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229532StripData.W"), new Formula.TypeArrow(Fin(21), new Formula.TypeArrow(Fin(31), Call("Int")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The 21 by 31 integer table is pinned by finite_certificate to the initial vector and twenty forward steps. Its row twenty satisfies the order-eighteen vector relation. The separate base_certificate pins the terminal scalar relation at row nineteen, which is needed for index twenty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("raw-successors"), DeclarationHandle.Create(Prefix + "raw_successors"), H("The frozen proper successor block"), StatementSource.FromAuthor(Disp(RawSuccessors())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The original class_fibres and finite_certificate are applied at saturated state (true,true). HardinA233255ShapeSymmetry.full_row gives weight 64 and the same final state for every row. Division by 64 therefore recovers the labelled three-colour proper successor counts."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(string value) => D(value.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(new Formula.Symbol(FormulaIdentifier.Create(part)))) }
        : new[] { Dot, Seq(Operatorname, Grp(new Formula.Symbol(FormulaIdentifier.Create(part)))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Q(name) : new Formula.Apply(Q(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(int size) => Call("Fin", Num(size.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula RowType() => new Formula.TypeArrow(Fin(6), Fin(3));
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumOver(string n, Formula type, Formula body) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));
    private static Formula RawSuccessors()
    {
        var p = V("p"); var r = V("r"); var j = V("j");
        var seen = Parenthesized(Seq(Call("true"), Comma, Sp, Call("true")));
        var predicate = And(Call("HardinThinGraphTransport.proper", r), And(Call("HardinThinGraphTransport.compatible", Call("true"), p, r), Eq(Call("HardinA233172DiagonalStrip.boundaryClass", seen, r), j)));
        return All("p", RowType(), Imp(Call("HardinThinGraphTransport.proper", p), All("j", Fin(11), Eq(Mul(Num("64"), SumOver("r", RowType(), Typed(Conditional(predicate, Num("1"), Num("0")), Call("Int")))), Call("HardinA233172DiagonalStrip.transfer", Call("HardinA233172DiagonalStrip.boundaryClass", seen, p), j)))));
    }
}

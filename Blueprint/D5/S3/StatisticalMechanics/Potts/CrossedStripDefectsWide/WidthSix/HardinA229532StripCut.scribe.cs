using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix;
internal sealed class HardinA229532StripCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripCut.";
    private const string Note = "D5/L/SpinModels/hardin2013a229532";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact width-six HDA transfer.", H("Width-six HDA transfer"), Blocks(
            Describe.Lean(DescribeId.Create("class-cut"), DeclarationHandle.Create(Prefix + "class_cut"),
                H("Structural proper-colouring cut"), StatementSource.FromAuthor(Disp(CutFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every pair of actual rows, residual budget d : Fin 2 and target s : Fin 20 in the matching proper block, the defect predicate is equivalent to properness, crossed compatibility and the published boundary class. A sum of nonnegative bond counts vanishes precisely when every bond has distinct endpoints. Only the single-row class correspondence is checked by finite kernel evaluation. All twenty proper target-column proofs consume this common equivalence and the original scanner successor counts. Nat.mod is natural-number modulo, the nonnegative remainder."))), DescribeRole.Theorem))));
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
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula CutFormula()
    {
        var p = V("p"); var d = V("d"); var r = V("r"); var s = V("s");
        var dv = Call("Fin.val", d); var sv = Call("Fin.val", s);
        Formula Data(string name, params Formula[] args) => Call("HardinA229532StripData." + name, args);
        var cost = Add(Call("DefectTransfer.bondDefects", Data("between"), p, r),
            Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), r, r));
        var block = Or(And(Eq(dv, Num("1")), Lt(sv, Num("10"))),
            And(Eq(dv, Num("0")), Le(Num("10"), sv)));
        var target = Typed(Call("Fin.castAdd", Num("11"), s), Fin(31));
        var boundary = Typed(Call("Fin.mk", Add(Call("Nat.mod", sv, Num("10")), Num("1"))), Fin(11));
        var identity = Iff(And(Le(cost, dv), Eq(Data("cl", r, Sub(dv, Parenthesized(cost))), target)),
            And(Call("HardinThinGraphTransport.proper", r),
                And(Call("HardinThinGraphTransport.compatible", Call("true"), p, r),
                    Eq(Call("HardinA233172DiagonalStrip.boundaryClass", Parenthesized(Seq(Call("true"), Comma, Sp, Call("true"))), r), boundary))));
        return All("p", RowType(), All("r", RowType(), All("d", Fin(2), All("s", Fin(20), Imp(block, identity)))));
    }

}

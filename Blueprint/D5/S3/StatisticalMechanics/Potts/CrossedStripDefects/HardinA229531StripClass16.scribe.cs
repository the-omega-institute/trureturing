using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229531StripClass16Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass16.";
    private const string Note = "D5/L/SpinModels/hardin2013a229531";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact width-five HDA transfer.", H("Width-five HDA transfer"), Blocks(
            Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
                H("Exact successor count"), StatementSource.FromAuthor(Disp(TransitionFormula(Num("16")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every actual row p : Fin 5 to Fin 3 and residual d : Fin 2 satisfying Valid p (Fin.val d), the number of successor rows r whose horizontal and cross-bond defects fit Fin.val d and whose new residual class is 16 equals T (cl p (Fin.val d)) 16. Nine source-colour fibres partition the finite kernel checks of this exact column of the 20 by 20 transfer. The combined successor identity applies this column in its corresponding target case."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(string value) => D(value.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(new Formula.Symbol(FormulaIdentifier.Create(part)))) }
        : new[] { Dot, Seq(Operatorname, Grp(new Formula.Symbol(FormulaIdentifier.Create(part)))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Q(name) : new Formula.Apply(Q(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(int size) => Call("Fin", Num(size.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula RowType() => new Formula.TypeArrow(Fin(5), Fin(3));
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula TransitionFormula(Formula target)
    {
        var p = V("p"); var d = V("d"); var r = V("r"); var dv = Call("Fin.val", d);
        Formula Data(string name, params Formula[] args) => Call("HardinA229531StripData." + name, args);
        var cost = Add(Call("DefectTransfer.bondDefects", Data("between"), p, r),
            Call("DefectTransfer.bondDefects", Data("horizontal"), r, r));
        var identity = Eq(SumOver("r", RowType(), Typed(Conditional(
            And(Le(cost, dv), Eq(Data("cl", r, Sub(dv, Parenthesized(cost))), target)), Num("1"), Num("0")), Call("Int"))),
            Data("T", Data("cl", p, dv), target));
        return All("p", RowType(), All("d", Fin(2), Imp(Data("Valid", p, dv), identity)));
    }

}

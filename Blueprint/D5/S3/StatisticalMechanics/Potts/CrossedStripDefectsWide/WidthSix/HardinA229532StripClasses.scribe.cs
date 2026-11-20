using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix;
internal sealed class HardinA229532StripClassesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClasses.";
    private const string Note = "D5/L/SpinModels/hardin2013a229532";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact width-six HDA transfer.", H("Width-six HDA transfer"), Blocks(
            Describe.Lean(DescribeId.Create("class-relabel"), DeclarationHandle.Create(Prefix + "class_relabel"),
                H("Colour permutation preserves the residual-budget class"),
                StatementSource.FromAuthor(Disp(ClassRelabelFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every natural residual budget and every six-column row, permuting the three colours preserves its class. The classifier depends only on equalities between colours and the number of monochromatic horizontal bonds."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bond-relabel"), DeclarationHandle.Create(Prefix + "bond_relabel"),
                H("Colour permutation preserves bond counts"),
                StatementSource.FromAuthor(Disp(BondRelabelFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every permutation of the three colours preserves the number of monochromatic bonds, for every finite bond set and pair of six-column rows."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
                H("All target classes"), StatementSource.FromAuthor(Disp(TransitionFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For every row p, residual d : Fin 2 and target s : Fin 31, Valid p (Fin.val d) implies that the permitted successor sum is T (cl p (Fin.val d)) s. A colour permutation transports a canonical representative back to the given row while preserving bond counts and the residual-budget class."))), DescribeRole.Theorem))));
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
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula ClassRelabelFormula()
    {
        var e = V("e"); var p = V("p"); var d = V("d");
        return All("e", Call("Equiv.Perm", Fin(3)), All("p", RowType(),
            All("d", Call("Nat"), Eq(Call("HardinA229532StripData.cl",
                Call("Function.comp", e, p), d), Call("HardinA229532StripData.cl", p, d)))));
    }
    private static Formula BondRelabelFormula()
    {
        var e = V("e"); var g = V("g"); var p = V("p"); var r = V("r");
        var pairType = Seq(Fin(6), Sp, Times, Sp, Fin(6));
        return All("e", Call("Equiv.Perm", Fin(3)),
            All("g", Call("Finset", Parenthesized(pairType)), All("p", RowType(), All("r", RowType(),
                Eq(Call("DefectTransfer.bondDefects", g,
                    Call("Function.comp", e, p), Call("Function.comp", e, r)),
                    Call("DefectTransfer.bondDefects", g, p, r))))));
    }
    private static Formula TransitionFormula()
    {
        var p = V("p"); var d = V("d"); var r = V("r"); var dv = Call("Fin.val", d);
        Formula Data(string name, params Formula[] args) => Call("HardinA229532StripData." + name, args);
        var cost = Add(Call("DefectTransfer.bondDefects", Call("HardinA229532StripData.between"), p, r),
            Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), r, r));
        var identity = Eq(SumOver("r", RowType(), Typed(Conditional(
            And(Le(cost, dv), Eq(Data("cl", r, Sub(dv, Parenthesized(cost))), V("s"))), Num("1"), Num("0")), Call("Int"))),
            Data("T", Data("cl", p, dv), V("s")));
        return All("p", RowType(), All("d", Fin(2), Imp(Data("Valid", p, dv), All("s", Fin(31), identity))));
    }

}

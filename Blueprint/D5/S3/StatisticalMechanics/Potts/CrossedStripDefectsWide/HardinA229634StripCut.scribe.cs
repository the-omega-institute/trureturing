using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide;
internal sealed class HardinA229634StripCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut.";
    private const string Note = "D5/L/SpinModels/hardin2013a229634";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-budget HDA extension.", H("Width-five two-defect transfer"), Blocks(
            Describe.Lean(DescribeId.Create("active-cut"), DeclarationHandle.Create(Prefix + "active_cut"),
                H("Inherited active-sector cut"), StatementSource.FromAuthor(Disp(Active())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For a positive residual, a transition into the inherited twenty classes is precisely an original one-defect transition with one less unit of residual budget. The proof checks only single-row arithmetic class facts, then handles arbitrary bond costs structurally."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inherited-counts"), DeclarationHandle.Create(Prefix + "inherited_counts"),
                H("Inherited successor counts"), StatementSource.FromAuthor(Disp(Counts())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every inherited column applies HardinA229531StripClasses.transition_counts through active_cut. At zero residual its sum and matrix block are both zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-cut"), DeclarationHandle.Create(Prefix + "zero_cut"),
                H("Proper terminal-sector cut"), StatementSource.FromAuthor(Disp(Zero())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For zero residual and one of the six proper targets, the new predicate is the original terminal proper predicate with indices shifted from six to twenty. No enumeration of row pairs is used."))), DescribeRole.Theorem))));
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

    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Cost() => Add(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), V("r"), V("r")));
    private static Formula Dv() => Call("Fin.val", V("d"));
    private static Formula Target() => Typed(Call("Fin.castAdd", Num("13"), V("j")), Fin(33));
    private static Formula Pred(Formula d, Formula target, string owner) => And(Le(Cost(), d), Eq(Call(owner + ".cl", V("r"), Sub(d, Parenthesized(Cost()))), target));
    private static Formula Active() => All("p", RowType(), All("r", RowType(), All("d", Fin(3), All("j", Fin(20), Imp(Lt(Num("0"), Dv()), Iff(Pred(Dv(), Target(), "HardinA229634StripData"), Pred(Sub(Dv(), Num("1")), V("j"), "HardinA229531StripData")))))));
    private static Formula Counts() => All("p", RowType(), All("d", Fin(3), Imp(Call("HardinA229634StripData.Valid", V("p"), Dv()), All("j", Fin(20), Eq(SumOver("r", RowType(), Typed(Conditional(Pred(Dv(), Target(), "HardinA229634StripData"), Num("1"), Num("0")), Call("Int"))), Call("HardinA229634StripData.T", Call("HardinA229634StripData.cl", V("p"), Dv()), Target()))))));
    private static Formula Zero() => All("p", RowType(), All("r", RowType(), All("j", Fin(6), Iff(Pred(Num("0"), Typed(Call("Fin.mk", Add(Num("20"), Call("Fin.val", V("j")))), Fin(33)), "HardinA229634StripData"), Pred(Num("0"), Typed(Call("Fin.mk", Add(Num("6"), Call("Fin.val", V("j")))), Fin(20)), "HardinA229531StripData")))));
}

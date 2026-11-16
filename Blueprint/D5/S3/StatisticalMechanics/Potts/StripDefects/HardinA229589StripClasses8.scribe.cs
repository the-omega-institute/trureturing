using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229589StripClasses8Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses8.";
    private const string Note = "D5/L/SpinModels/hardin2013a229589";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exactly 1 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("transition-counts"),
                DeclarationHandle.Create(Prefix + "transition_counts"), H("Output-class transition sums"),
                StatementSource.FromAuthor(Disp(All("s", Call("Fin", Num("28")), Imp(And(Leq(Num("16"), Call("Fin.val", V("s"))), Lt(Call("Fin.val", V("s")), Num("18"))), All("p", Call("HardinA229589StripData.Row"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229589StripData.Valid", V("p"), Call("Fin.val", V("d"))), Eq(SumOver("r", Call("HardinA229589StripData.Row"), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("HardinA229589StripData.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229589StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229589StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Add(Call("DefectTransfer.bondDefects", Call("HardinA229589StripData.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229589StripData.horizontal"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229589StripData.T"), Call("HardinA229589StripData.cl", V("p"), Call("Fin.val", V("d"))), V("s")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The indicated class interval is checked over every admissible boundary and budget."))), DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}

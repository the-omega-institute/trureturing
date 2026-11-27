using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class HardinA229604StripCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripCut.";
    private const string Note = "D5/L/SpinModels/hardin2013a229604";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("active-cut"), DeclarationHandle.Create(Prefix + "active_cut"),
                H("active cut"), StatementSource.FromAuthor(Disp(All("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("c", Call("Nat"), All("d", Call("Fin", Num("3")), All("j", Call("Fin", Num("42")), Imp(Lt(Num("0"), Call("Fin.val", V("d"))), Iff(And(Leq(V("c"), Call("Fin.val", V("d"))), Eq(Call("HardinA229604StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), V("c"))), Call("Fin.castAdd", Num("54"), V("j")))), And(Leq(V("c"), Sub(Call("Fin.val", V("d")), Num("1"))), Eq(Call("HardinA229457StripData.cl", V("r"), Sub(Sub(Call("Fin.val", V("d")), Num("1")), V("c"))), V("j"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A transition into an old active class leaves positive residual budget. Subtracting one from both budgets gives exactly the old class condition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("leading-counts"), DeclarationHandle.Create(Prefix + "leading_counts"),
                H("leading counts"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229604StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("j", Call("Fin", Num("42")), Eq(SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Typed(Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229604StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Parenthesized(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), Call("Fin.castAdd", Num("54"), V("j")))), Num("1"), Num("0")), Call("Int"))), Call("HardinA229604StripData.T", Call("HardinA229604StripData.cl", V("p"), Call("Fin.val", V("d"))), Call("Fin.castAdd", Num("54"), V("j")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading 42 target classes use the old transition counts. Zero residual budget cannot enter any of those classes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("terminal-counts"), DeclarationHandle.Create(Prefix + "terminal_counts"),
                H("terminal counts"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Imp(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("p"), V("p")), Num("1")), All("j", Call("Fin", Num("32")), Eq(SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Typed(Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Num("0")), Eq(Call("HardinA229604StripData.cl", V("r"), Sub(Num("0"), Parenthesized(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), Call("Fin.castAdd", Num("22"), Call("Fin.natAdd", Num("42"), V("j"))))), Num("1"), Num("0")), Call("Int"))), Call("HardinA229604StripData.T", Call("HardinA229604StripData.cl", V("p"), Num("0")), Call("Fin.castAdd", Num("22"), Call("Fin.natAdd", Num("42"), V("j")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The copied terminal block counts zero-cost successors of rows with at most one horizontal defect, using the old terminal-sector identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("one-defect-counts"), DeclarationHandle.Create(Prefix + "one_defect_counts"),
                H("One-defect counts"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Imp(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("p"), V("p")), Num("0")), All("j", Call("Fin", Num("32")), Eq(SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Typed(Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Num("1")), Eq(Call("HardinA229604StripData.cl", V("r"), Sub(Num("1"), Parenthesized(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), Call("Fin.castAdd", Num("22"), Call("Fin.natAdd", Num("42"), V("j"))))), Num("1"), Num("0")), Call("Int"))), Call("HardinA229604StripData.T", Call("HardinA229604StripData.cl", V("p"), Num("1")), Call("Fin.castAdd", Num("22"), Call("Fin.natAdd", Num("42"), V("j")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For a source row with no horizontal defect and residual budget one, successors contributing to the sum have cost zero or one. Cost zero leaves a class below 42, whereas cost one shifts the old terminal class by 32. Larger costs contribute zero. The 10 by 32 crossing block is exactly the corresponding one-defect matrix block, so HardinA229457StripClasses.transition_counts at budget one supplies the sum without any canonical-row hypothesis."))), DescribeRole.Theorem))));
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Call("if"), Sp, Parenthesized(c), Sp, Call("then"), Sp, Parenthesized(y), Sp, Call("else"), Sp, Parenthesized(n)));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
}

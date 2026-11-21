using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class HardinA229457StripCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripCut.";
    private const string Note = "D5/L/SpinModels/hardin2013a229457";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("crossed-proper-slot"), DeclarationHandle.Create(Prefix + "crossedProperSlot"),
                H("Crossed proper slot"), StatementSource.FromAuthor(Disp(
                    Typed(Call("HardinA229457StripCut.crossedProperSlot"), Arrow(Call("Fin", Num("20")), Call("Fin", Num("20")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("In slots 0 through 9, the values are (9, 6, 3, 8, 4, 1, 7, 0, 2, 5), in order. In slots 10 through 19, add 10 to each of these values. Fin.append joins the two blocks, and proper_class_map relates each slot to its crossed classifier value."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("proper-class-map"), DeclarationHandle.Create(Prefix + "proper_class_map"),
                H("Proper-class correspondence"), StatementSource.FromAuthor(Disp(ProperClassMap())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The two classifiers agree on membership in the corresponding proper-row slots at each of the two residual budgets. Fin.castAdd embeds a finite index preserving its value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("class-cut"), DeclarationHandle.Create(Prefix + "class_cut"),
                H("class cut"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Fin", Num("2")), All("s", Call("Fin", Num("20")), Imp(Or(And(Eq(Call("Fin.val", V("d")), Num("1")), Lt(Call("Fin.val", V("s")), Num("10"))), And(Eq(Call("Fin.val", V("d")), Num("0")), Leq(Num("10"), Call("Fin.val", V("s"))))), Iff(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229457StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Parenthesized(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), Typed(Call("Fin.castAdd", Num("22"), V("s")), Call("Fin", Num("42"))))), And(Call("HardinThinGraphTransport.proper", V("r")), And(All("i", Call("Fin", Num("6")), Ne(App(V("p"), V("i")), App(V("r"), V("i")))), Eq(Call("HardinA233127SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), V("r")), Typed(Call("Fin.mk", Add(Call("Nat.mod", Call("Fin.val", V("s")), Num("10")), Num("1"))), Call("Fin", Num("11")))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A transition staying in the matching proper sector has zero cost. Since both defect counts are nonnegative, zero cost means that every horizontal and vertical bond has distinct endpoints. Nat.mod is the nonnegative natural remainder after division by ten."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proper-counts"), DeclarationHandle.Create(Prefix + "proper_counts"),
                H("proper counts"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Fin", Num("2")), Imp(Call("HardinThinGraphTransport.proper", V("p")), All("s", Call("Fin", Num("20")), Imp(Or(And(Eq(Call("Fin.val", V("d")), Num("1")), Lt(Call("Fin.val", V("s")), Num("10"))), And(Eq(Call("Fin.val", V("d")), Num("0")), Leq(Num("10"), Call("Fin.val", V("s"))))), Eq(SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Typed(Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229457StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Parenthesized(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), Typed(Call("Fin.castAdd", Num("22"), V("s")), Call("Fin", Num("42"))))), Num("1"), Num("0")), Call("Int"))), Call("HardinA229457StripData.T", Call("HardinA229457StripData.cl", V("p"), Call("Fin.val", V("d"))), Typed(Call("Fin.castAdd", Num("22"), V("s")), Call("Fin", Num("42")))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The matching proper-column sum is supplied by the saturated scanner identity. Natural remainder chooses its original class."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("active-counts"), DeclarationHandle.Create(Prefix + "active_counts"),
                H("active counts"), StatementSource.FromAuthor(Disp(All("j", Call("Fin", Num("10")), All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229457StripData.Valid", V("p"), Call("Fin.val", V("d"))), Eq(SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Typed(Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229457StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Parenthesized(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), Call("Fin.castAdd", Num("32"), V("j")))), Num("1"), Num("0")), Call("Int"))), Call("HardinA229457StripData.T", Call("HardinA229457StripData.cl", V("p"), Call("Fin.val", V("d"))), Call("Fin.castAdd", Num("32"), V("j")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading ten target classes use the original proper-colouring matrix. A zero residual budget cannot enter those classes."))), DescribeRole.Theorem))));
    private static Formula ProperClassMap()
    {
        var r = V("r");
        var d = Call("Fin.val", V("d"));
        var s = V("s");
        var squareSlot = Typed(Call("Fin.castAdd", Num("22"), s), Call("Fin", Num("42")));
        var crossedSlot = Typed(Call("Fin.castAdd", Num("11"),
            Call("HardinA229457StripCut.crossedProperSlot", s)), Call("Fin", Num("31")));
        return All("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))),
            All("d", Call("Fin", Num("2")), All("s", Call("Fin", Num("20")),
                Iff(Eq(Call("HardinA229457StripData.cl", r, d), squareSlot),
                    Eq(Call("HardinA229532StripData.cl", r, d), crossedSlot)))));
    }
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
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Call("if"), Sp, Parenthesized(c), Sp, Call("then"), Sp, Parenthesized(y), Sp, Call("else"), Sp, Parenthesized(n)));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
}

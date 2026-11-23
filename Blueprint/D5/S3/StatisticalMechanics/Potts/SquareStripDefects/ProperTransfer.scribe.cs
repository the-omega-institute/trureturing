using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class ProperTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.";
    private const string Note = "D5/L/SpinModels/hardin2013a229457";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("between"), DeclarationHandle.Create(Prefix + "between"),
                H("between"), StatementSource.FromAuthor(Disp(Eq(Call("ProperTransfer.between"), Call("Finset.diag", Typed(Call("Finset.univ"), Call("Finset", Call("Fin", Num("6")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each pair joins the same column in consecutive rows; horizontal bonds join adjacent columns in one row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("cl"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Eq(Call("ProperTransfer.cl", V("p")), Typed(Call("Fin.mk", Sub(Call("Fin.val", Call("HardinA233127SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), V("p"))), Num("1"))), Call("Fin", Num("10"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The ten saturated proper-row classes use indices zero through nine. Natural subtraction truncates at zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"),
                H("T"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num("10")), All("j", Call("Fin", Num("10")), Eq(Call("ProperTransfer.T", V("i"), V("j")), Call("Int.ediv", Call("HardinA233127SquareStrip.transfer", Typed(Call("Fin.mk", Add(Call("Fin.val", V("i")), Num("1"))), Call("Fin", Num("11"))), Typed(Call("Fin.mk", Add(Call("Fin.val", V("j")), Num("1"))), Call("Fin", Num("11")))), Num("64"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("This is the ten by ten saturated submatrix of the square scanner, with integer division by 64."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("raw-successors"), DeclarationHandle.Create(Prefix + "raw_successors"),
                H("raw successors"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Imp(Call("HardinThinGraphTransport.proper", V("p")), All("j", Call("Fin", Num("11")), Eq(Mul(Num("64"), SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Typed(Conditional(And(Call("HardinThinGraphTransport.proper", V("r")), And(All("i", Call("Fin", Num("6")), Ne(App(V("p"), V("i")), App(V("r"), V("i")))), Eq(Call("HardinA233127SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), V("r")), V("j")))), Num("1"), Num("0")), Call("Int")))), Call("HardinA233127SquareStrip.transfer", Call("HardinA233127SquareStrip.boundaryClass", Pair(Call("true"), Call("true")), V("p")), V("j")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every labelled three-colour row has exactly 64 individual-colour scanner realizations. The scanner sum is transported through that fibre identity and the existing exact row-count theorem."))), DescribeRole.Theorem))));
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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Call("if"), Sp, Parenthesized(c), Sp, Call("then"), Sp, Parenthesized(y), Sp, Call("else"), Sp, Parenthesized(n)));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
}

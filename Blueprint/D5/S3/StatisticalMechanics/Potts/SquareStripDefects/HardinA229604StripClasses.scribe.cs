using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class HardinA229604StripClassesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripClasses.";
    private const string Note = "D5/L/SpinModels/hardin2013a229604";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
                H("transition counts"), StatementSource.FromAuthor(Disp(All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229604StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("s", Call("Fin", Num("96")), Eq(SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("3"))), Typed(Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229604StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Parenthesized(Add(Call("DefectTransfer.bondDefects", Call("ProperTransfer.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), V("r"), V("r")))))), V("s"))), Num("1"), Num("0")), Call("Int"))), Call("HardinA229604StripData.T", Call("HardinA229604StripData.cl", V("p"), Call("Fin.val", V("d"))), V("s"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The old active block is supplied by its structural cut identity. Colour permutations preserve all equality tests and bond defects, transporting the canonical source-row identities to every labelled source row."))), DescribeRole.Theorem))));
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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Call("if"), Sp, Parenthesized(c), Sp, Call("then"), Sp, Parenthesized(y), Sp, Call("else"), Sp, Parenthesized(n)));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
}

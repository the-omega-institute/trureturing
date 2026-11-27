using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class HardinA229457StripPowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers.";
    private const string Note = "D5/L/SpinModels/hardin2013a229457";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("steps"), DeclarationHandle.Create(Prefix + "steps"),
                H("steps"), StatementSource.FromAuthor(Disp(And(Eq(Call("HardinA229457StripData.W", Num("0")), Call("HardinA229457StripData.initial")), All("i", Call("Fin", Num("25")), All("s", Call("Fin", Num("42")), Eq(Call("HardinA229457StripData.W", Call("Fin.succ", V("i")), V("s")), Call("Matrix.vecMul", Call("HardinA229457StripData.W", Call("Fin.castSucc", V("i"))), Call("HardinA229457StripData.T"), V("s")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading ten coordinates follow from the A233127 continuation powers. The transfer has zero lower-left block, and its leading block satisfies 64 times initial i times ProperTransfer.T i j = initial j times the transposed A233127 transfer entry. Induction gives 64 to the power k times W k j = initial j times the A233127 continuation at k and class j+1, and proves the defining integer division exact. Only the 32 one-defect coordinates use the finite step certificates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("relation"), DeclarationHandle.Create(Prefix + "relation"),
                H("relation"), StatementSource.FromAuthor(Disp(All("s", Call("Fin", Num("42")), Eq(Call("HardinA229457StripData.W", Num("15"), V("s")), SumOver("j", Call("Fin", Num("14")), Mul(App(Vector(Parenthesized(Seq(Minus, Num("266256"))), Num("2220864"), Parenthesized(Seq(Minus, Num("8262712"))), Num("18139608"), Parenthesized(Seq(Minus, Num("26188161"))), Num("26218062"), Parenthesized(Seq(Minus, Num("18693789"))), Num("9593166"), Parenthesized(Seq(Minus, Num("3537110"))), Num("924894"), Parenthesized(Seq(Minus, Num("167163"))), Num("20016"), Parenthesized(Seq(Minus, Num("1482"))), Num("60")), V("j")), Call("HardinA229457StripData.W", Typed(Call("Fin.mk", Add(Num("1"), Call("Fin.val", V("j")))), Call("Fin", Num("26"))), V("s")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The order-fourteen polynomial annihilates every coordinate of the forward vector starting at row index one."))), DescribeRole.Theorem))));
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Vector(params Formula[] a) => Seq(new Formula[] { Bang, OpenBracket }.Concat(a.SelectMany((x,i) => i==0 ? new[] {x} : new[] {Comma, Sp, x})).Append(CloseBracket).ToArray());
}

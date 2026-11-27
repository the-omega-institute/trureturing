using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects;
internal sealed class HardinA229604StripPowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers.";
    private const string Note = "D5/L/SpinModels/hardin2013a229604";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("steps"), DeclarationHandle.Create(Prefix + "steps"),
                H("steps"), StatementSource.FromAuthor(Disp(And(Eq(Call("HardinA229604StripData.W", Num("0")), Call("HardinA229604StripData.initial")), All("i", Call("Fin", Num("24")), All("s", Call("Fin", Num("96")), Eq(Call("HardinA229604StripData.W", Call("Fin.succ", V("i")), V("s")), Call("Matrix.vecMul", Call("HardinA229604StripData.W", Call("Fin.castSucc", V("i"))), Call("HardinA229604StripData.T"), V("s")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every one of the 24 forward steps holds in all 96 coordinates; the first 42 coordinates use the one-defect forward identities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("relation"), DeclarationHandle.Create(Prefix + "relation"),
                H("relation"), StatementSource.FromAuthor(Disp(All("s", Call("Fin", Num("96")), Eq(Call("HardinA229604StripData.W", Num("24"), V("s")), SumOver("j", Call("Fin", Num("21")), Mul(App(Vector(Num("137388096"), Parenthesized(Seq(Minus, Num("1718948736"))), Num("9979813584"), Parenthesized(Seq(Minus, Num("35729023024"))), Num("88409012652"), Parenthesized(Seq(Minus, Num("160604595216"))), Num("222060410955"), Parenthesized(Seq(Minus, Num("239066083215"))), Num("203308881255"), Parenthesized(Seq(Minus, Num("137758028106"))), Num("74677395474"), Parenthesized(Seq(Minus, Num("32398609896"))), Num("11214272853"), Parenthesized(Seq(Minus, Num("3076398702"))), Num("661896144"), Parenthesized(Seq(Minus, Num("110021385"))), Num("13836015"), Parenthesized(Seq(Minus, Num("1278486"))), Num("83214"), Parenthesized(Seq(Minus, Num("3573"))), Num("90")), V("j")), Call("HardinA229604StripData.W", Typed(Call("Fin.mk", Add(Num("3"), Call("Fin.val", V("j")))), Call("Fin", Num("25"))), V("s")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The order-21 polynomial annihilates the forward vector starting at index three. On the old 42 coordinates it follows from the order-fourteen polynomial by multiplication with its degree-seven factor; only the 54 new coordinates need finite arithmetic evaluation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("initial-relation"), DeclarationHandle.Create(Prefix + "initial_relation"),
                H("initial relation"), StatementSource.FromAuthor(Disp(Eq(Call("dotProduct", Call("HardinA229604StripData.W", Num("23")), Call("HardinA229604StripData.terminal")), SumOver("j", Call("Fin", Num("21")), Mul(App(Vector(Num("137388096"), Parenthesized(Seq(Minus, Num("1718948736"))), Num("9979813584"), Parenthesized(Seq(Minus, Num("35729023024"))), Num("88409012652"), Parenthesized(Seq(Minus, Num("160604595216"))), Num("222060410955"), Parenthesized(Seq(Minus, Num("239066083215"))), Num("203308881255"), Parenthesized(Seq(Minus, Num("137758028106"))), Num("74677395474"), Parenthesized(Seq(Minus, Num("32398609896"))), Num("11214272853"), Parenthesized(Seq(Minus, Num("3076398702"))), Num("661896144"), Parenthesized(Seq(Minus, Num("110021385"))), Num("13836015"), Parenthesized(Seq(Minus, Num("1278486"))), Num("83214"), Parenthesized(Seq(Minus, Num("3573"))), Num("90")), V("j")), Call("dotProduct", Call("HardinA229604StripData.W", Typed(Call("Fin.mk", Add(Num("2"), Call("Fin.val", V("j")))), Call("Fin", Num("25")))), Call("HardinA229604StripData.terminal"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("At the preceding index, the polynomial has zero scalar terminal readout. Together with the vector identity, this includes exactly the first claimed height 24."))), DescribeRole.Theorem))));
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

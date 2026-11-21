using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers;
internal sealed class HardinA229604StripStep5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep5.";
    private const string Note = "D5/L/SpinModels/hardin2013a229604";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-lattice strip transfer.", H("Six-column square-lattice strip"), Blocks(
            Describe.Lean(DescribeId.Create("steps"), DeclarationHandle.Create(Prefix + "steps"),
                H("steps"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num("6")), All("s", Call("Fin", Num("18")), Eq(Call("HardinA229604StripData.W", Typed(Call("Fin.mk", Add(Add(Num("6"), Call("Fin.val", V("i"))), Num("1"))), Call("Fin", Num("25"))), Typed(Call("Fin.mk", Add(Num("78"), Call("Fin.val", V("s")))), Call("Fin", Num("96")))), Call("Matrix.vecMul", Call("HardinA229604StripData.W", Typed(Call("Fin.mk", Add(Num("6"), Call("Fin.val", V("i")))), Call("Fin", Num("25")))), Call("HardinA229604StripData.T"), Typed(Call("Fin.mk", Add(Num("78"), Call("Fin.val", V("s")))), Call("Fin", Num("96"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("These integer identities give six consecutive forward steps in 18 new terminal coordinates."))), DescribeRole.Theorem))));
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
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
}

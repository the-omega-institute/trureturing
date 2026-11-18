using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229691StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2013a229691";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("structural-certificate"),
                DeclarationHandle.Create(Prefix + "structural_certificate"), H("Structural and forward certificate"),
                StatementSource.FromAuthor(Disp(And(All("p", Call("HardinA229583StripData.Boundary"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229691StripData.Valid", V("p"), Call("Fin.val", V("d"))), Eq(App(Call("HardinA229691StripData.terminal"), Call("HardinA229691StripData.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("p", Call("HardinA229583StripData.Boundary"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229691StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("r", Call("HardinA229583StripData.Row"), Imp(Leq(Add(Call("HardinA229583StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Call("HardinA229691StripData.Valid", Call("HardinA229583StripData.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229583StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")))))))))), And(All("r", Call("HardinA229583StripData.Row"), Imp(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")), Num("2")), Call("HardinA229691StripData.Valid", Call("HardinA229583StripData.boundary", V("r")), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")))))), And(All("s", Call("Fin", Num("27")), Eq(SumOver("r", Call("HardinA229583StripData.Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")), Num("2")), Eq(Call("HardinA229691StripData.cl", Call("HardinA229583StripData.boundary", V("r")), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229691StripData.initial"), V("s")))), And(And(Eq(App(Call("HardinA229691StripData.W"), Num("0")), Call("HardinA229691StripData.initial")), All("i", Call("Fin", Num("7")), Eq(App(Call("HardinA229691StripData.W"), Call("Fin.succ", V("i"))), Call("Matrix.vecMul", App(Call("HardinA229691StripData.W"), Call("Fin.castSucc", V("i"))), Call("HardinA229691StripData.T"))))), Eq(App(Call("HardinA229691StripData.W"), Num("7")), SumOver("j", Call("Fin", Num("6")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("5832"))), Call("Matrix.vecCons", Num("14580"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("13122"))), Call("Matrix.vecCons", Num("4995"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("729"))), Call("Matrix.vecCons", Num("45"), Call("Matrix.vecEmpty"))))))), V("j")), App(Call("HardinA229691StripData.W"), Call("Fin.mk", Add(Num("1"), Call("Fin.val", V("j"))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Acceptance, budgets, initial weights and the forward polynomial relation."))), DescribeRole.Theorem))));

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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}

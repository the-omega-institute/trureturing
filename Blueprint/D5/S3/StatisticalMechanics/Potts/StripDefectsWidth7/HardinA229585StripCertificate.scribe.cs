using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7;
internal sealed class HardinA229585StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2013a229585";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("structural-certificate"),
                DeclarationHandle.Create(Prefix + "structural_certificate"), H("Structural and forward-table certificate"),
                StatementSource.FromAuthor(Disp(And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229585StripData.Valid", V("p"), Call("Fin.val", V("d"))), Eq(App(Call("HardinA229585StripData.terminal"), Call("HardinA229585StripData.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("p", V("Boundary"), All("d", Call("Fin", Num("2")), Imp(Call("HardinA229585StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("r", V("Row"), Imp(Leq(Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Call("HardinA229585StripData.Valid", Call("HardinA229585StripData.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229585StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r")))))))))), And(All("r", V("Row"), Imp(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r")), Num("1")), Call("HardinA229585StripData.Valid", Call("HardinA229585StripData.boundary", V("r")), Sub(Num("1"), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r")))))), And(All("s", Call("Fin", Num("72")), Eq(SumOver("r", V("Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r")), Num("1")), Eq(Call("HardinA229585StripData.cl", Call("HardinA229585StripData.boundary", V("r")), Sub(Num("1"), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229585StripData.initial"), V("s")))), And(And(Eq(App(Call("HardinA229585StripData.W"), Num("0")), Call("HardinA229585StripData.initial")), All("i", Call("Fin", Num("10")), Eq(App(Call("HardinA229585StripData.W"), Call("Fin.succ", V("i"))), Call("Matrix.vecMul", App(Call("HardinA229585StripData.W"), Call("Fin.castSucc", V("i"))), Call("HardinA229585StripData.T"))))), Eq(App(Call("HardinA229585StripData.W"), Num("10")), SumOver("j", Call("Fin", Num("8")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("656100"))), Call("Matrix.vecCons", Num("1574640"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("1513404"))), Call("Matrix.vecCons", Num("750384"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("206469"))), Call("Matrix.vecCons", Num("31428"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("2466"))), Call("Matrix.vecCons", Num("84"), Call("Matrix.vecEmpty"))))))))), V("j")), App(Call("HardinA229585StripData.W"), Call("Fin.mk", Add(Num("2"), Call("Fin.val", V("j"))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("All initial, terminal, budget and forward-table identities are checked over the displayed finite domains."))), DescribeRole.Theorem))));

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

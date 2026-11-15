using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7;
internal sealed class HardinA229585StripHistogramDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripHistogram.";
    private const string Note = "D5/L/SpinModels/hardin2013a229585";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exact finite histograms for the width-seven one-defect strip.")),
            Describe.Lean(DescribeId.Create("input"),
                DeclarationHandle.Create(Prefix + "Input"), H("Boundary, budget and destination class"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229585StripHistogram.Input"), Product(V("Boundary"), Product(Call("Fin", Num("2")), Call("Fin", Num("72"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The budget is zero or one and the output class ranges over all 72 quotient states."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("histogram"),
                DeclarationHandle.Create(Prefix + "histogram"), H("Filtered transition histogram"),
                StatementSource.FromAuthor(Disp(All("x", V("Input"), Eq(Call("HardinA229585StripHistogram.histogram", V("x")), Call("Finset.sum", Call("Finset.filter", Fn("r", V("Row"), Leq(Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r")), Num("1"))), Call("Finset.univ")), Fn("r", V("Row"), Conditional(And(Leq(Add(Call("HardinA229585StripData.cross", Call("Prod.fst", V("x")), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", Call("Prod.fst", Call("Prod.snd", V("x"))))), Eq(Call("HardinA229585StripData.cl", Call("HardinA229585StripData.boundary", V("r")), Sub(Call("Fin.val", Call("Prod.fst", Call("Prod.snd", V("x")))), Add(Call("HardinA229585StripData.cross", Call("Prod.fst", V("x")), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))))), Call("Prod.snd", Call("Prod.snd", V("x"))))), Num("1"), Num("0")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Rows with more than one horizontal defect cannot contribute to either residual budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sum-filtered"),
                DeclarationHandle.Create(Prefix + "sum_filtered"), H("Exact removal of horizontally inadmissible rows"),
                StatementSource.FromAuthor(Disp(All("x", V("Input"), Eq(SumOver("r", V("Row"), Conditional(And(Leq(Add(Call("HardinA229585StripData.cross", Call("Prod.fst", V("x")), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", Call("Prod.fst", Call("Prod.snd", V("x"))))), Eq(Call("HardinA229585StripData.cl", Call("HardinA229585StripData.boundary", V("r")), Sub(Call("Fin.val", Call("Prod.fst", Call("Prod.snd", V("x")))), Add(Call("HardinA229585StripData.cross", Call("Prod.fst", V("x")), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), V("r"), V("r"))))), Call("Prod.snd", Call("Prod.snd", V("x"))))), Num("1"), Num("0"))), Call("HardinA229585StripHistogram.histogram", V("x")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The equality retains every original row: omitted rows have zero contribution because their horizontal defect count alone exceeds the budget."))), DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}

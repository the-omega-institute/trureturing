using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229691StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229691";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229691Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("5"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229583StripData.horizontal"), Call("HardinA229583StripData.antidiagonal"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("5")), App(V("A"), Pair(V("i"), V("j"))))))), Num("2")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("5"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("5"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Canonical is the original HardinA233177Canonical.Canonical predicate, with order lifted through finProdFinEquiv to retain literal row-major order. The filter enumerates all n by k arrays. The ordinal i*k+j is the original row-major order, matching the row transfer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"),
                DeclarationHandle.Create(Prefix + "finite_certificate"), H("Exact finite transfer certificate"),
                StatementSource.FromAuthor(Disp(And(All("p", Call("HardinA229583StripData.Boundary"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229691StripData.Valid", V("p"), Call("Fin.val", V("d"))), Eq(App(Call("HardinA229691StripData.terminal"), Call("HardinA229691StripData.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("p", Call("HardinA229583StripData.Boundary"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229691StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("r", Call("HardinA229583StripData.Row"), Imp(Leq(Add(Call("HardinA229583StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Call("HardinA229691StripData.Valid", Call("HardinA229583StripData.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229583StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")))))))))), And(All("p", Call("HardinA229583StripData.Boundary"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229691StripData.Valid", V("p"), Call("Fin.val", V("d"))), All("s", Call("Fin", Num("27")), Eq(SumOver("r", Call("HardinA229583StripData.Row"), Conditional(And(Leq(Add(Call("HardinA229583StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229691StripData.cl", Call("HardinA229583StripData.boundary", V("r")), Sub(Call("Fin.val", V("d")), Add(Call("HardinA229583StripData.cross", V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229691StripData.T"), Call("HardinA229691StripData.cl", V("p"), Call("Fin.val", V("d"))), V("s"))))))), And(All("r", Call("HardinA229583StripData.Row"), Imp(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")), Num("2")), Call("HardinA229691StripData.Valid", Call("HardinA229583StripData.boundary", V("r")), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")))))), And(All("s", Call("Fin", Num("27")), Eq(SumOver("r", Call("HardinA229583StripData.Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")), Num("2")), Eq(Call("HardinA229691StripData.cl", Call("HardinA229583StripData.boundary", V("r")), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("HardinA229583StripData.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229691StripData.initial"), V("s")))), And(And(Eq(App(Call("HardinA229691StripData.W"), Num("0")), Call("HardinA229691StripData.initial")), All("i", Call("Fin", Num("7")), Eq(App(Call("HardinA229691StripData.W"), Call("Fin.succ", V("i"))), Call("Matrix.vecMul", App(Call("HardinA229691StripData.W"), Call("Fin.castSucc", V("i"))), Call("HardinA229691StripData.T"))))), Eq(App(Call("HardinA229691StripData.W"), Num("7")), SumOver("j", Call("Fin", Num("6")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("5832"))), Call("Matrix.vecCons", Num("14580"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("13122"))), Call("Matrix.vecCons", Num("4995"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("729"))), Call("Matrix.vecCons", Num("45"), Call("Matrix.vecEmpty"))))))), V("j")), App(Call("HardinA229691StripData.W"), Call("Fin.mk", Add(Num("1"), Call("Fin.val", V("j")))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The clauses certify acceptance, budget preservation, transition sums, initial admissibility and weights, every forward step and the polynomial relation. The last index has value b+j, bounded by the table length."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("The registered integer recurrence"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA229691Strip.a", Add(V("n"), Num("8")))), Sub(Add(Sub(Add(Sub(Mul(Num("45"), CastInt(Call("HardinA229691Strip.a", Add(V("n"), Num("7"))))), Mul(Num("729"), CastInt(Call("HardinA229691Strip.a", Add(V("n"), Num("6")))))), Mul(Num("4995"), CastInt(Call("HardinA229691Strip.a", Add(V("n"), Num("5")))))), Mul(Num("13122"), CastInt(Call("HardinA229691Strip.a", Add(V("n"), Num("4")))))), Mul(Num("14580"), CastInt(Call("HardinA229691Strip.a", Add(V("n"), Num("3")))))), Mul(Num("5832"), CastInt(Call("HardinA229691Strip.a", Add(V("n"), Num("2")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The row transfer counts labelled arrays. the original row-major canonical representatives have six labelled realizations. Multiplication propagates the certified vector relation to every further length."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229691"), ResolutionKind.Proved)))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}

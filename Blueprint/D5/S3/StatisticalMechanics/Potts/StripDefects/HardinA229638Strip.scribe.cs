using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229638StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229638";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("type-row"),
                DeclarationHandle.Create(Prefix + "Row"), H("Column letters"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229638Strip.Row"), Arrow(Call("Fin", Num("2")), Call("Fin", Num("3")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A transfer letter is one column of the literal array."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("No internal column bonds"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229638Strip.horizontal"), Call("Finset.empty")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every registered bond joins consecutive columns; none lies within a column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229638Strip.Row"), All("d", V("Nat"), Iff(Call("HardinA229638Strip.Valid", V("p"), V("d")), Leq(V("d"), Num("2"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The remaining budget is at most the registered exact budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Equality and budget classes"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229638Strip.Row"), All("d", V("Nat"), Eq(Call("HardinA229638Strip.cl", V("p"), V("d")), Conditional(And(Eq(V("d"), Num("2")), Eq(App(V("p"), Num("0")), App(V("p"), Num("1")))), Num("0"), Conditional(And(Eq(V("d"), Num("2")), Ne(App(V("p"), Num("0")), App(V("p"), Num("1")))), Num("1"), Conditional(And(Eq(V("d"), Num("1")), Eq(App(V("p"), Num("0")), App(V("p"), Num("1")))), Num("2"), Conditional(And(Eq(V("d"), Num("1")), Ne(App(V("p"), Num("0")), App(V("p"), Num("1")))), Num("3"), Conditional(And(Eq(V("d"), Num("0")), Eq(App(V("p"), Num("0")), App(V("p"), Num("1")))), Num("4"), Num("5"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Global colour permutations preserve the equality pattern of the retained column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("T"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229638Strip.T"), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("2"), Call("Matrix.vecCons", Num("2"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("4"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("1"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("4"), Call("Matrix.vecCons", Num("2"), Call("Matrix.vecCons", Num("2"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("2"), Call("Matrix.vecCons", Num("2"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("1"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("4"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("2"), Call("Matrix.vecCons", Num("2"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("1"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecEmpty")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading four-state block and the one-defect transition block call HardinA229535Strip.T. Fin.append adds only the two new two-defect rows. The other tables give initial weights, terminal acceptance and successive forward weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("initial"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229638Strip.initial"), Call("Matrix.vecCons", Num("3"), Call("Matrix.vecCons", Num("6"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecEmpty")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("terminal"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229638Strip.terminal"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("1"), Call("Matrix.vecCons", Num("1"), Call("Matrix.vecEmpty")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("W"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229638Strip.W"), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("3"), Call("Matrix.vecCons", Num("6"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("12"), Call("Matrix.vecCons", Num("6"), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("24"), Call("Matrix.vecCons", Num("12"), Call("Matrix.vecCons", Num("24"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("30"), Call("Matrix.vecCons", Num("24"), Call("Matrix.vecCons", Num("24"), Call("Matrix.vecCons", Num("24"), Call("Matrix.vecCons", Num("60"), Call("Matrix.vecCons", Num("180"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("84"), Call("Matrix.vecCons", Num("60"), Call("Matrix.vecCons", Num("72"), Call("Matrix.vecCons", Num("144"), Call("Matrix.vecCons", Num("348"), Call("Matrix.vecCons", Num("384"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("228"), Call("Matrix.vecCons", Num("168"), Call("Matrix.vecCons", Num("288"), Call("Matrix.vecCons", Num("384"), Call("Matrix.vecCons", Num("1200"), Call("Matrix.vecCons", Num("1728"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("624"), Call("Matrix.vecCons", Num("456"), Call("Matrix.vecCons", Num("960"), Call("Matrix.vecCons", Num("1248"), Call("Matrix.vecCons", Num("4464"), Call("Matrix.vecCons", Num("5184"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecCons", Call("Matrix.vecCons", Num("1704"), Call("Matrix.vecCons", Num("1248"), Call("Matrix.vecCons", Num("3168"), Call("Matrix.vecCons", Num("3744"), Call("Matrix.vecCons", Num("15024"), Call("Matrix.vecCons", Num("17328"), Call("Matrix.vecEmpty"))))))), Call("Matrix.vecEmpty"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229638Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", Num("2")), Call("Fin", V("n"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229638Strip.horizontal"), Call("HardinA229535Strip.between"), Call("List.ofFn", Fn("j", Call("Fin", V("n")), Fn("i", Call("Fin", Num("2")), App(V("A"), Pair(V("i"), V("j"))))))), Num("2")), All("p", Product(Call("Fin", Num("2")), Call("Fin", V("n"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", Num("2")), Call("Fin", V("n"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), V("n")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), V("n")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Canonical is the original HardinA233177Canonical.Canonical predicate, with order lifted through finProdFinEquiv to retain literal row-major order. The filter enumerates all k by n arrays. The ordinal i*n+j is the original row-major order, including when transfer sweeps columns."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"),
                DeclarationHandle.Create(Prefix + "finite_certificate"), H("Exact finite transfer certificate"),
                StatementSource.FromAuthor(Disp(And(All("p", Call("HardinA229638Strip.Row"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229638Strip.Valid", V("p"), Call("Fin.val", V("d"))), Eq(App(Call("HardinA229638Strip.terminal"), Call("HardinA229638Strip.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("p", Call("HardinA229638Strip.Row"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229638Strip.Valid", V("p"), Call("Fin.val", V("d"))), All("r", Call("HardinA229638Strip.Row"), Imp(Leq(Add(Call("DefectTransfer.bondDefects", Call("HardinA229535Strip.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Call("HardinA229638Strip.Valid", V("r"), Sub(Call("Fin.val", V("d")), Add(Call("DefectTransfer.bondDefects", Call("HardinA229535Strip.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r")))))))))), And(All("p", Call("HardinA229638Strip.Row"), All("d", Call("Fin", Num("3")), Imp(Call("HardinA229638Strip.Valid", V("p"), Call("Fin.val", V("d"))), All("s", Call("Fin", Num("6")), Eq(SumOver("r", Call("HardinA229638Strip.Row"), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("HardinA229535Strip.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r"))), Call("Fin.val", V("d"))), Eq(Call("HardinA229638Strip.cl", V("r"), Sub(Call("Fin.val", V("d")), Add(Call("DefectTransfer.bondDefects", Call("HardinA229535Strip.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229638Strip.T"), Call("HardinA229638Strip.cl", V("p"), Call("Fin.val", V("d"))), V("s"))))))), And(All("r", Call("HardinA229638Strip.Row"), Imp(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r")), Num("2")), Call("HardinA229638Strip.Valid", V("r"), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r")))))), And(All("s", Call("Fin", Num("6")), Eq(SumOver("r", Call("HardinA229638Strip.Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r")), Num("2")), Eq(Call("HardinA229638Strip.cl", V("r"), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("HardinA229638Strip.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), App(Call("HardinA229638Strip.initial"), V("s")))), And(And(Eq(App(Call("HardinA229638Strip.W"), Num("0")), Call("HardinA229638Strip.initial")), All("i", Call("Fin", Num("6")), Eq(App(Call("HardinA229638Strip.W"), Call("Fin.succ", V("i"))), Call("Matrix.vecMul", App(Call("HardinA229638Strip.W"), Call("Fin.castSucc", V("i"))), Call("HardinA229638Strip.T"))))), Eq(App(Call("HardinA229638Strip.W"), Num("6")), SumOver("j", Call("Fin", Num("6")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Num("8"), Call("Matrix.vecCons", Num("24"), Call("Matrix.vecCons", Num("12"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("16"))), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("6"))), Call("Matrix.vecCons", Num("6"), Call("Matrix.vecEmpty"))))))), V("j")), App(Call("HardinA229638Strip.W"), Call("Fin.mk", Add(Num("0"), Call("Fin.val", V("j")))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The clauses certify acceptance, budget preservation, transition sums, initial admissibility and weights, every forward step and the polynomial relation. The last index has value b+j, bounded by the table length."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("The registered integer recurrence"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA229638Strip.a", Add(V("n"), Num("7")))), Add(Add(Add(Sub(Sub(Mul(Num("6"), CastInt(Call("HardinA229638Strip.a", Add(V("n"), Num("6"))))), Mul(Num("6"), CastInt(Call("HardinA229638Strip.a", Add(V("n"), Num("5")))))), Mul(Num("16"), CastInt(Call("HardinA229638Strip.a", Add(V("n"), Num("4")))))), Mul(Num("12"), CastInt(Call("HardinA229638Strip.a", Add(V("n"), Num("3")))))), Mul(Num("24"), CastInt(Call("HardinA229638Strip.a", Add(V("n"), Num("2")))))), Mul(Num("8"), CastInt(Call("HardinA229638Strip.a", Add(V("n"), Num("1")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The column transfer counts labelled arrays. Coordinate exchange is an equivalence of labelled arrays; the original row-major canonical representatives have six labelled realizations. Multiplication propagates the certified vector relation to every further length."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229638"), ResolutionKind.Proved)))));

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
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
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

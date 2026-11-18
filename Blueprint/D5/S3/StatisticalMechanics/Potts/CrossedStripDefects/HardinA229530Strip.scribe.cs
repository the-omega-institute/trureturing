using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229530StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229530";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal HDA colourings and exact defect transfer.", H("Hardin A229530: exact defect recurrence"),
        Blocks(Paragraph(Text("The literal array has n rows, 4 columns and exactly 1 monochromatic HDA bonds. Rows are swept by an exact-budget transfer with 10 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. The frozen four_class_certificate supplies proper transitions through scanner_fibres at saturated Seen flags, an exact budget/class cut and division by sixteen. The remaining defective-source and defect-consuming entries are computed separately.")),
            Describe.Lean(DescribeId.Create("shared-between"), DeclarationHandle.Create(Prefix + "between"),
                H("Shared between"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA229530Strip.between"), Seq(Call("HardinA229582Strip.antidiagonal"), Sp, Cup, Sp, Call("Finset.image", Call("Prod.swap"), Call("HardinA229582Strip.antidiagonal")))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The exact HDA bonds between consecutive rows, shared with the two-defect extension."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-valid"), DeclarationHandle.Create(Prefix + "Valid"),
                H("Shared Valid"), StatementSource.FromAuthor(Disp(ValidFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The one-defect residual-budget domain, reused after subtracting one from the two-defect residual budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("Shared cl"), StatementSource.FromAuthor(Disp(ClassFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The 10 equality-and-budget classes. The two-defect extension embeds this class index as its active leading sector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-transfer"), DeclarationHandle.Create(Prefix + "T"),
                H("Shared T"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229530Strip.T"), Call("Matrix", Fin(10), Fin(10), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The 10 by 10 exact integer transfer, pinned by finite_certificate. The two-defect extension uses this matrix as its leading block."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("Shared initial"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229530Strip.initial"), Arrow(Fin(10), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The raw labelled initial vector on Fin 10, shared as the leading initial sector and pinned by finite_certificate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-forward-weights"), DeclarationHandle.Create(Prefix + "W"),
                H("Shared W"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229530Strip.W"), Arrow(Fin(7), Arrow(Fin(10), Call("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The Fin 7 cached forward prefix on Fin 10, shared by the two-defect extension and pinned by finite_certificate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shared-finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
                H("Shared finite_certificate"), StatementSource.FromAuthor(Disp(FiniteCertificateFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Exact terminal values, validity preservation, successor and initial counts, cached forward recurrence and polynomial relation. The two-defect extension reuses its active successor and initial projections."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("raw-successors"), DeclarationHandle.Create(Prefix + "raw_successors"),
                H("Proper successor counts from saturated scanner fibres"), StatementSource.FromAuthor(Disp(RawSuccessorsFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("At saturated Seen flags, sixteen times every actual proper three-colour successor count is the corresponding HardinSourceContinuations.M entry. The theorem applies the frozen four_class_certificate through scanner_fibres and preserves all target classes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229530Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("4"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229582Strip.horizontal"), Call("HardinA229530Strip.between"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("4")), App(V("A"), Pair(V("i"), V("j"))))))), Num("1")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("4"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("4"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("4")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("4")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The registered all-index recurrence"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(AsInt(Call("HardinA229530Strip.a", Add(V("n"), Num("6")))), Sub(Add(Sub(Mul(Num("14"), AsInt(Call("HardinA229530Strip.a", Add(V("n"), Num("5"))))), Mul(Num("57"), AsInt(Call("HardinA229530Strip.a", Add(V("n"), Num("4")))))), Mul(Num("56"), AsInt(Call("HardinA229530Strip.a", Add(V("n"), Num("3")))))), Mul(Num("16"), AsInt(Call("HardinA229530Strip.a", Add(V("n"), Num("2")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The recurrence holds at every index at least 6. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229530"), ResolutionKind.Proved)))));

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
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));

    private static Formula AsInt(Formula value) => Parenthesized(Seq(value, Colon, Sp, Call("Int")));

    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula RowType() => Arrow(Fin(4), Fin(3));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));
    private static Formula Vector(params Formula[] entries) => Seq(new Formula[] { Bang, OpenBracket }
        .Concat(entries.SelectMany((f,i) => i == 0 ? new[] { f } : new[] { Comma, Sp, f })).Append(CloseBracket).ToArray());

    private static Formula ValidFormula()
    {
        var p = V("p"); var d = V("d");
        return All("p", RowType(), All("d", Call("Nat"), Eq(Call("HardinA229530Strip.Valid", p, d),
            Parenthesized(And(Le(d, Num("1")), Le(Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), p, p), Sub(Num("1"), d)))))));
    }

    private static Formula ClassFormula()
    {
        var p = V("p"); var d = V("d");
        return All("p", RowType(), All("d", Call("Nat"), Eq(Typed(Call("HardinA229530Strip.cl", p, d), Fin(10)),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), p, p), Num("0")), Eq(Call("HardinSourceContinuations.sourceClass", Pair(Call("true"), Call("true")), p), Num("1")))), Num("0"),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), p, p), Num("0")), Eq(Call("HardinSourceContinuations.sourceClass", Pair(Call("true"), Call("true")), p), Num("2")))), Num("1"),
            Conditional(And(Eq(d, Num("1")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), p, p), Num("0")), Eq(Call("HardinSourceContinuations.sourceClass", Pair(Call("true"), Call("true")), p), Num("3")))), Num("2"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), p, p), Num("0")), Eq(Call("HardinSourceContinuations.sourceClass", Pair(Call("true"), Call("true")), p), Num("1")))), Num("3"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), p, p), Num("0")), Eq(Call("HardinSourceContinuations.sourceClass", Pair(Call("true"), Call("true")), p), Num("2")))), Num("4"),
            Conditional(And(Eq(d, Num("0")), And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), p, p), Num("0")), Eq(Call("HardinSourceContinuations.sourceClass", Pair(Call("true"), Call("true")), p), Num("3")))), Num("5"),
            Conditional(And(Eq(d, Num("0")), Or(And(Eq(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Eq(App(p, Num("1")), App(p, Num("3"))), Ne(App(p, Num("2")), App(p, Num("3")))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Eq(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), Eq(App(p, Num("2")), App(p, Num("3")))))))))), Num("6"),
            Conditional(And(Eq(d, Num("0")), Or(And(Eq(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), Ne(App(p, Num("2")), App(p, Num("3")))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Ne(App(p, Num("0")), App(p, Num("3"))), And(Ne(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), Eq(App(p, Num("2")), App(p, Num("3")))))))))), Num("7"),
            Conditional(And(Eq(d, Num("0")), Or(And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), Ne(App(p, Num("2")), App(p, Num("3")))))))), And(Ne(App(p, Num("0")), App(p, Num("1"))), And(Ne(App(p, Num("0")), App(p, Num("2"))), And(Eq(App(p, Num("0")), App(p, Num("3"))), And(Eq(App(p, Num("1")), App(p, Num("2"))), And(Ne(App(p, Num("1")), App(p, Num("3"))), Ne(App(p, Num("2")), App(p, Num("3")))))))))), Num("8"),
            Num("9")))))))))))));
    }

    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));

    private static Formula FiniteCertificateFormula()
    {
        var p = V("p"); var d = V("d"); var r = V("r"); var target = V("s");
        var i = V("i"); var j = V("j"); var dv = Call("Fin.val", d);
        Formula Own(string name, params Formula[] args) => Call("HardinA229530Strip." + name, args);
        Formula Horizontal(Formula row) => Call("DefectTransfer.bondDefects", Call("HardinA229582Strip.horizontal"), row, row);
        var cost = Add(Call("DefectTransfer.bondDefects", Own("between"), p, r), Horizontal(r));
        var residual = Sub(dv, Parenthesized(cost));
        Formula UnderValid(Formula body) => All("p", RowType(), All("d", Fin(2), Imp(Own("Valid", p, dv), body)));
        var terminal = Typed(Vector(Num("0"),Num("0"),Num("0"),Num("1"),Num("1"),Num("1"),Num("1"),Num("1"),Num("1"),Num("1")), Arrow(Fin(10), Call("Int")));
        var acceptance = UnderValid(Eq(App(terminal, Own("cl", p, dv)),
            Typed(Conditional(Eq(dv, Num("0")), Num("1"), Num("0")), Call("Int"))));
        var preservation = UnderValid(All("r", RowType(), Imp(Le(cost, dv), Own("Valid", r, residual))));
        var successor = UnderValid(All("s", Fin(10), Eq(SumOver("r", RowType(),
            Typed(Conditional(And(Le(cost, dv), Eq(Own("cl", r, residual), target)), Num("1"), Num("0")), Call("Int"))),
            Own("T", Own("cl", p, dv), target))));
        var initialValid = All("r", RowType(), Imp(Le(Horizontal(r), Num("1")),
            Own("Valid", r, Sub(Num("1"), Horizontal(r)))));
        var initialCount = All("s", Fin(10), Eq(SumOver("r", RowType(), Typed(Conditional(
            And(Le(Horizontal(r), Num("1")), Eq(Own("cl", r, Sub(Num("1"), Horizontal(r))), target)),
            Num("1"), Num("0")), Call("Int"))), Own("initial", target)));
        var forward = And(Eq(Own("W", Num("0")), Own("initial")), All("i", Fin(6),
            Eq(Own("W", Call("Fin.succ", i)), Call("Matrix.vecMul", Own("W", Call("Fin.castSucc", i)), Own("T")))));
        var polynomial = Eq(Own("W", Num("6")), SumOver("j", Fin(4), Call("HSMul.hSMul",
            Typed(App(Vector(Parenthesized(Seq(Minus, Num("16"))),Num("56"),Parenthesized(Seq(Minus, Num("57"))),Num("14")), j), Call("Int")),
            Own("W", Typed(Call("Fin.mk", Add(Num("2"), Call("Fin.val", j))), Fin(7))))));
        return And(acceptance, And(preservation, And(successor, And(initialValid,
            And(initialCount, And(forward, polynomial))))));
    }

    private static Formula RawSuccessorsFormula()
    {
        var p = V("p"); var q = V("q"); var j = V("j");
        var seen = Pair(Call("true"), Call("true"));
        Formula Class(Formula row) => Call("HardinSourceContinuations.sourceClass", seen, row);
        var indicator = Typed(Conditional(And(Call("HardinThinGraphTransport.proper", q),
            And(Call("HardinThinGraphTransport.compatible", Call("true"), p, q), Eq(Class(q), j))), Num("1"), Num("0")), Call("Int"));
        return All("p", RowType(), Imp(Call("HardinThinGraphTransport.proper", p), All("j", Fin(4),
            Eq(Mul(Num("16"), Parenthesized(SumOver("q", RowType(), indicator))),
                Call("HardinSourceContinuations.M", Class(p), j)))));
    }

}

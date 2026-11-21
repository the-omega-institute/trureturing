using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide;
internal sealed class HardinA229532StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229532";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal HDA colourings and exact defect transfer.", H("Hardin A229532: exact defect recurrence"),
        Blocks(Paragraph(Text("The literal array has n rows, 6 columns and exactly one monochromatic HDA bond. Rows are swept by an exact-budget transfer with 31 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. Finite certificates check the exact image and every defect entry.")),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229532Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("6"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229584StripData.horizontal"), Call("HardinA229532StripData.between"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("6")), App(V("A"), Pair(V("i"), V("j"))))))), Num("1")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("6"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("6"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("6")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("6")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
                H("Exact one-defect transfer certificate"), StatementSource.FromAuthor(Disp(FiniteCertificateFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first three clauses give terminal acceptance, preservation of validity after a guarded move, and all weighted successor counts. The remaining clauses give first-row validity and multiplicities, the twenty forward steps, and the signed relation for the last vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The registered all-index recurrence"), StatementSource.FromAuthor(Disp(RecurrenceFormula())),

                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The recurrence is an identity in the integers at every index at least 20. DefectTransfer.lumped_count and forward_shift propagate the vector relation from row twenty. A separate terminal scalar certificate at row nineteen supplies the first index twenty; the full vector relation is not claimed there. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229532"), ResolutionKind.Proved)))));

    private static Formula FiniteCertificateFormula()
    {
        var row = Call("HardinA229584StripData.Row");
        var state = Call("Fin", Num("31"));
        var p = V("p");
        var d = Call("Fin.val", V("d"));
        var r = V("r");
        var s = V("s");
        var i = V("i");
        var j = V("j");
        Formula Data(string name, params Formula[] args) => Call("HardinA229532StripData." + name, args);
        Formula Horizontal(Formula x) => Call("DefectTransfer.bondDefects", Call("HardinA229584StripData.horizontal"), x, x);
        Formula ForValid(Formula clause) => All("p", row, All("d", Call("Fin", Num("2")), Imp(Data("Valid", p, d), clause)));
        var cost = Add(Call("DefectTransfer.bondDefects", Data("between"), p, r), Horizontal(r));
        var affordable = AtMost(cost, d);
        var remaining = Sub(d, cost);
        var firstAffordable = AtMost(Horizontal(r), Num("1"));
        var firstRemaining = Sub(Num("1"), Horizontal(r));
        var terminal = ForValid(Eq(Data("terminal", Data("cl", p, d)), Conditional(Eq(d, Num("0")), Num("1"), Num("0"))));
        var closed = ForValid(All("r", row, Imp(affordable, Data("Valid", r, remaining))));
        var counts = ForValid(All("s", state, Eq(
            SumOver("r", row, Conditional(And(affordable, Eq(Data("cl", r, remaining), s)), Num("1"), Num("0"))),
            Data("T", Data("cl", p, d), s))));
        var firstValid = All("r", row, Imp(firstAffordable, Data("Valid", r, firstRemaining)));
        var firstCounts = All("s", state, Eq(
            SumOver("r", row, Conditional(And(firstAffordable, Eq(Data("cl", r, firstRemaining), s)), Num("1"), Num("0"))),
            Data("initial", s)));
        var powers = And(Eq(Data("W", Num("0")), Data("initial")),
            All("i", Call("Fin", Num("20")), Eq(Data("W", Call("Fin.succ", i)),
                Call("Matrix.vecMul", Data("W", Call("Fin.castSucc", i)), Data("T")))));
        int[] coefficients = [-25, 240, 204, -6334, 6468, 42628, -83203, -34136, 160400,
            -40816, -108224, 56184, 23849, -19128, 340, 1854, -436, 36];
        Formula SignedInt(int value) => value < 0 ? Seq(Minus, Num((-value).ToString())) : Num(value.ToString());
        var vector = Seq(new Formula[] { Bang, OpenBracket }.Concat(coefficients.SelectMany((value, index) =>
            index == 0 ? new[] { SignedInt(value) } : new[] { Comma, Sp, SignedInt(value) })).Append(CloseBracket).ToArray());
        var relation = Eq(Data("W", Num("20")), SumOver("j", Call("Fin", Num("18")),
            Seq(App(vector, j), Sp, Cdot, Sp, Data("W", Add(Num("2"), Call("Fin.val", j))))));
        return And(terminal, And(closed, And(counts, And(firstValid, And(firstCounts, And(powers, relation))))));
    }

    private static Formula AtMost(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Conditional(Formula guard, Formula yes, Formula no) =>
        Parenthesized(Seq(Call("if"), Sp, guard, Sp, Call("then"), Sp, yes, Sp, Call("else"), Sp, no));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Parenthesized(body));

    private static Formula RecurrenceFormula()
    {
        int[] coefficients = [36, -436, 1854, 340, -19128, 23849, 56184, -108224, -40816, 160400, -34136, -83203, 42628, 6468, -6334, 204, 240, -25];
        Formula Term(int i) => Mul(Num((coefficients[i] < 0 ? -coefficients[i] : coefficients[i]).ToString(System.Globalization.CultureInfo.InvariantCulture)),
            AsInt(Call("HardinA229532Strip.a", Add(V("n"), Num((19-i).ToString(System.Globalization.CultureInfo.InvariantCulture))))));
        Formula rhs = Term(0);
        for (int i = 1; i < coefficients.Length; i++) rhs = coefficients[i] < 0 ? Sub(rhs, Term(i)) : Add(rhs, Term(i));
        return All("n", Call("Nat"), Eq(AsInt(Call("HardinA229532Strip.a", Add(V("n"), Num("20")))), rhs));
    }
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

}

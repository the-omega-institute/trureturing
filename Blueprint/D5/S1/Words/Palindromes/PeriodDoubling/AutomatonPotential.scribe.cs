using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class AutomatonPotentialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Backward and forward path induction turn edge inequalities into bounds for every accepted input.", H("Integer Potentials on Nondeterministic Runs"), Blocks(
        Describe.Lean(DescribeId.Create("pd-automatonpotential-pathcharge"),
            DeclarationHandle.Create(Prefix + "pathCharge"), H("Integer charge of a run"),
            StatementSource.FromAuthor(ChargeFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Charge is defined on the existing NFA.Path proof object. The empty run has charge zero, and a cons run adds the first edge charge to the tail charge. The equations retain every carrier and all constructor arguments."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-automatonpotential-accepted-path-bound"),
            DeclarationHandle.Create(Prefix + "accepted_path_bound"), H("Total potentials control every accepting run"),
            StatementSource.FromAuthor(BoundFormula(false)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Start potentials are nonnegative. Each transition dominates its predecessor potential plus the edge charge. Accepted states have a bounded potential plus terminal offset. Induction on the actual run proves the bound at arbitrary length."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("pd-automatonpotential-accepted-path-bound-partial"),
            DeclarationHandle.Create(Prefix + "accepted_path_bound_partial"), H("Partial potentials control every accepting run"),
            StatementSource.FromAuthor(BoundFormula(true)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A present potential at a successor propagates backwards to a present predecessor with the edge inequality. Every accepted state has a present bounded potential. Backwards path induction reaches the source and bounds the entire charge."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Prop() => Ty("Prop");
    private static Formula SetOf(Formula a) => Call("Set", a);
    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NotF(Formula a) => new Formula.Not(a);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula At(Formula f, Formula x) => Call("val", f, x);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));


    private static Formula Sigma() => V("S");
    private static Formula Path(Formula s, Formula t, Formula xs) => Call("Path", V("M"), s, t, xs);
    private static Formula Charges() => Fn(Sigma(), Fn(V("A"), Fn(Sigma(), Z())));
    private static Formula Core(Formula body) => All("A", Ty("Type"), All("S", Ty("Type"),
        All("M", Call("NFA", V("A"), Sigma()), All("charge", Charges(), body))));
    private static Formula PC(Formula p) => Call("pathCharge", V("charge"), p);
    private static Formula ChargeFormula()
    {
        var empty = All("s", Sigma(), Eqn(PC(Call("nil", V("s"))), D(0)));
        var step = Eqn(PC(Call("cons", V("q"), V("s"), V("t"), V("a"), V("xs"), V("h"), V("p"))),
            Add(Call("val", V("charge"), V("s"), V("a"), V("q")), PC(V("p"))));
        step = All("p", Path(V("q"), V("t"), V("xs")), step);
        step = All("h", Mem(V("q"), Call("step", V("M"), V("s"), V("a"))), step);
        step = All("xs", ListOf(V("A")), step);
        step = All("a", V("A"), step);
        step = All("t", Sigma(), step);
        step = All("s", Sigma(), step);
        step = All("q", Sigma(), step);
        return Disp(Core(And(empty, step)));
    }
    private static Formula BoundFormula(bool partial)
    {
        var next = Mem(V("q"), Call("step", V("M"), V("s"), V("a")));
        var sourceMember = Mem(V("s"), Call("start", V("M")));
        var goalMember = Mem(V("t"), Call("accept", V("M")));
        Formula source, edge, goal;
        if (partial)
        {
            source = All("s", Sigma(), Imp(sourceMember, All("V", Z(),
                Imp(Eqn(At(V("potential"), V("s")), Call("some", V("V"))), LeF(D(0), V("V"))))));
            var transfer = All("W", Z(), Imp(Eqn(At(V("potential"), V("q")), Call("some", V("W"))),
                Ex("V", Z(), And(Eqn(At(V("potential"), V("s")), Call("some", V("V"))),
                    LeF(Add(V("V"), Call("val", V("charge"), V("s"), V("a"), V("q"))), V("W"))))));
            edge = All("s", Sigma(), All("q", Sigma(), All("a", V("A"), Imp(next, transfer))));
            goal = All("t", Sigma(), Imp(goalMember, Ex("W", Z(), And(
                Eqn(At(V("potential"), V("t")), Call("some", V("W"))),
                LeF(Add(V("W"), At(V("offset"), V("t"))), V("B"))))));
        }
        else
        {
            source = All("s", Sigma(), Imp(sourceMember, LeF(D(0), At(V("potential"), V("s")))));
            edge = All("s", Sigma(), All("q", Sigma(), All("a", V("A"), Imp(next,
                LeF(Add(At(V("potential"), V("s")), Call("val", V("charge"), V("s"), V("a"), V("q"))),
                    At(V("potential"), V("q")))))));
            goal = All("t", Sigma(), Imp(goalMember,
                LeF(Add(At(V("potential"), V("t")), At(V("offset"), V("t"))), V("B"))));
        }
        var conclusion = All("s", Sigma(), All("t", Sigma(), All("xs", ListOf(V("A")),
            Imp(And(sourceMember, goalMember), All("p", Path(V("s"), V("t"), V("xs")),
                LeF(Add(PC(V("p")), At(V("offset"), V("t"))), V("B")))))));
        var body = Imp(And(source, edge, goal), conclusion);
        body = All("B", Z(), body);
        body = All("offset", Fn(Sigma(), Z()), body);
        body = All("potential", Fn(Sigma(), partial ? Call("Option", Z()) : Z()), body);
        return Disp(Core(body));
    }

}

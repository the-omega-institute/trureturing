using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseSignedStreamsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every accepted base-transducer path emits nonadjacent signed digits with an exact radix-two value.", H("Signed Digit Streams of the Base Transducer"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basesignedstreams-pathoutputs"),
            DeclarationHandle.Create(Prefix + "pathOutputs"), H("Ordered transition observations"),
            StatementSource.FromAuthor(OutputDefinition()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("pathOutputs reads one transition observation per edge in path order. The nil constructor emits the empty list; cons prepends emit s a q to the observations of the remaining path. Its automaton, alphabet, state and output types are arbitrary."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basesignedstreams-base-path-sparse-signed-digits"),
            DeclarationHandle.Create(Prefix + "base_path_sparse_signed_digits"), H("Exact sparse signed-digit reconstruction"),
            StatementSource.FromAuthor(StreamFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("output selects the fourth edge coordinate and target-state component 12 when true, or the third edge coordinate and component 10 when false. Every emitted digit is minus one, zero, or one; consecutive digits cannot both be nonzero. Folding z + 2 x gives twice the encoded rounded half. The first emitted digit is the dummy zero at position minus one. All path lengths are allowed. This is a statement about accepted graph paths; completeness for actual palindrome cuts and the Q interpretation remain separate obligations."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));
    private static Formula OptionalHead(Formula xs) =>
        Call("ite", Eqn(xs, Seq(OpenBracket, CloseBracket)), Call("none"),
            Call("some", DottedCall("List", "head", xs)));

    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(owner == "NFA.Path"
            ? Seq(V("NFA"), Dot, V("Path"), Dot, V(member))
            : Seq(V(owner), Dot, V(member)))), [.. args]);

    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);


    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula Cons(Formula a, Formula xs) => Call("cons", a, xs);
    private static Formula Entry(Formula state, Formula k) => Call("getD", OptionalIndex(state, k), D(0));
    private static Formula Outputs(Formula emit, Formula path) => Call("pathOutputs", V("M"), emit, path);
    private static Formula Common(Formula body) =>
        All("alpha", Ty("Type"), All("sigma", Ty("Type"), All("beta", Ty("Type"),
        All("M", Call("NFA", V("alpha"), V("sigma")),
        All("emit", Fn(V("sigma"), Fn(V("alpha"), Fn(V("sigma"), V("beta")))), body)))));
    private static Formula OutputDefinition()
    {
        var nil = Common(All("s", V("sigma"), Eqn(
            Outputs(V("emit"), DottedCall("NFA.Path", "nil", V("s"))), ListNil())));
        var cons = Eqn(Outputs(V("emit"), DottedCall("NFA.Path", "cons", V("q"), V("s"), V("t"),
            V("a"), V("xs"), V("hstep"), V("p"))),
            Cons(Call("emit", V("s"), V("a"), V("q")), Outputs(V("emit"), V("p"))));
        var edge = Mem(V("q"), Call("step", V("M"), V("s"), V("a")));
        var quantified = All("s", V("sigma"), All("q", V("sigma"), All("t", V("sigma"),
            All("a", V("alpha"), All("xs", ListOf(V("alpha")), All("hstep", edge,
            All("p", Call("Path", V("M"), V("q"), V("t"), V("xs")), cons)))))));
        return Disp(And(nil, Common(quantified)));
    }
    private static Formula StreamFormula()
    {
        var auto = Call("baseAutomaton", V("charge"));
        var target = Call("fst", Call("baseTable", Call("val", V("q"))));
        var emit = Seq(LambdaLower, Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp,
            OpenBracket, Alphabet(), CloseBracket, Sp, V("q"), Colon, Call("Fin", D(1,4,9,2)),
            Sp, Mapsto, Sp, Entry(target, Ite(V("output"), D(1,2), D(1,0))));
        var stream = Call("pathOutputs", auto, emit, V("p"));
        var coefficients = All("z", Z(), Imp(Mem(V("z"), stream),
            new Formula.Logic(Eqn(V("z"), NegF(D(1))), FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(V("z"), D(0)), FormulaLogicOperator.Or, Eqn(V("z"), D(1))))));
        var sparse = Call("IsChain", stream, Lam("a", Z(), Lam("b", Z(),
            new Formula.Logic(Eqn(V("a"), D(0)), FormulaLogicOperator.Or, Eqn(V("b"), D(0))))));
        var value = Call("foldr", Lam("z", Z(), Lam("acc", Z(), Add(V("z"), Mul(D(2), V("acc"))))), D(0), stream);
        var edge = V("a");
        var bit = Ite(V("output"), Call("snd", Call("snd", Call("snd", edge))),
            Call("fst", Call("snd", Call("snd", edge))));
        var raw = Call("foldr", Lam("a", Alphabet(), Lam("acc", Z(), Add(bit, Mul(D(2), V("acc"))))), D(0), V("xs"));
        var source = Call("fst", Call("baseTable", Call("val", V("s"))));
        var identity = Eqn(value, Mul(D(2), Parenthesized(Add(raw, Entry(source, Ite(V("output"), D(3), D(2)))))));
        var body = All("p", Call("Path", auto, V("s"), V("t"), V("xs")),
            And(coefficients, sparse, identity, Eqn(OptionalHead( stream), Call("some", D(0)))));
        body = Imp(And(Mem(V("s"), Call("start", auto)), Mem(V("t"), Call("accept", auto))), body);
        return Disp(All("charge", Ty("Bool"), All("output", Ty("Bool"), All("s", Call("Fin", D(1,4,9,2)),
            All("t", Call("Fin", D(1,4,9,2)), All("xs", ListOf(Alphabet()), body))))));
    }
}

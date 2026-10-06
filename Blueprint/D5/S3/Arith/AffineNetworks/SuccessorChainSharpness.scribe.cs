using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AffineNetworks;

internal sealed class SuccessorChainSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual named successor chain attains the original modular stopping depth.",
        H("Successor-chain stopping sharpness"),
        Blocks(Describe.Lean(
            DescribeId.Create("successor-chain-sharpness"),
            DeclarationHandle.Create(
                "D5/S3/Arith/AffineNetworks/SuccessorChainSharpness.successor_chain_sharpness"),
            H("Original recurrence and complete actual-source transcripts"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every natural N≥2 and m≥2, the theorem constructs one actual Network C. " +
                    "Its vertex and named-edge types are equivalent to Fin N and Fin (N−1). " +
                    "Edge j has source rank j and destination rank j+1, multiplier 1 and offset 0. " +
                    "The root has rank 0, the last vertex rank N−1, the ambient modulus is m, " +
                    "and exactly the last vertex has port m; every other port is 1.")),
                Paragraph(Text(
                    "Notation in the authored formula follows the original Lean objects: Nat is ℕ, " +
                    "Equiv(A,B) is A≃B, Type(u) uses the theorem's arbitrary universe u, and " +
                    "a binder displayed with ∈ is a typed binder. Network, NPath, networkQuiver, " +
                    "iterate, pathRun and portRead are the original AffineModularStopping declarations. " +
                    "Dotted names and numeric projections are the original record fields and tuple " +
                    "projections; in particular val(iv(v)) is a rank, while v itself lies in C.V. " +
                    "List, Sum, Option and Prod are the corresponding Lean types. Σ v:T,U is the " +
                    "dependent pair type Sigma, angle brackets construct such pairs, parentheses " +
                    "construct ordinary pairs, brackets construct lists, and ++ is List.append. " +
                    "A colon is a type ascription; if(b,x,y) means if b then x else y. " +
                    "Path.nil, path.cons, path.comp, Sum.inl, Sum.inr, none, some and HEq are " +
                    "the original constructors, path operations and heterogeneous equality. " +
                    "The typed let and match bind state and next locally, with their usual Lean " +
                    "stop/append branches. The trace endpoint arguments are implicit in Lean; " +
                    "their dependent function domain is displayed explicitly here.")),
                Paragraph(Text(
                    "The independently defined original gcd/lcm iterate is evaluated for every " +
                    "depth n and every vertex of rank i. It equals 1 when i+n<N−1 and m otherwise. " +
                    "The proof computes the actual outgoing named-edge subtype: empty at the last " +
                    "vertex and a singleton elsewhere. Depth induction propagates the terminal port; " +
                    "no replacement recurrence or assumed path characterization is used.")),
                Paragraph(Text(
                    "Every actual path from v to w satisfies rank(w)=rank(v)+length(path), and " +
                    "its original phase run preserves every t in the full source ZMod m. " +
                    "An actual root-to-last named-edge path is constructed with length N−1. " +
                    "Its terminal port returns the original canonical phase residue and separates " +
                    "the same sources 0 and 1 used in every shorter experiment.")),
                Paragraph(Text(
                    "For every shorter root path, every factorization into a prefix and a suffix " +
                    "has prefix port 1 and equal actual reads for 0 and 1. The empty prefix gives " +
                    "the initial root read; the empty suffix gives the final read of that path. " +
                    "The chronological trace has typed vertex-port events and named-edge events. " +
                    "It starts with the actual root read and appends each actual edge followed by " +
                    "the read of the same continuously transported phase at its destination. " +
                    "The displayed trace equations use the same C and trace bound in the statement.")),
                new DocumentBlock.DisplayFormula(TraceFormula()),
                Paragraph(Text(
                    "For every internal-control type K and every deterministic choice function " +
                    "of public vertex, current control and obtained chronological trace, an actual " +
                    "executor is constructed. Choices are either stop or an original legal outgoing " +
                    "arrow with its next control state. The returned state retains the actual path " +
                    "and control. At zero it is the root empty path and the supplied common control; " +
                    "each next step either stays stopped or appends the chosen named arrow. " +
                    "The executed path length is at most the step count. At every count below N−1, " +
                    "both sources produce equal paths, controls, complete chronological traces and " +
                    "next choices. This is proved by induction from actual prefix reads, rather " +
                    "than assuming transcript equality. A common external random seed may be " +
                    "included in K; the theorem states deterministic equality for each fixed seed.")),
                Paragraph(Text("At every shorter depth "),
                    Math(Seq(F.Id("n"), Lt, F.Id("N"), Minus, D(1))),
                    Text(
                        ", the same original root iterate is 1, while its value at N−1 is m≠1. " +
                        "The explicit delayed distinguishing experiment therefore prevents any " +
                        "smaller uniform stopping depth. This statement concerns the prescribed " +
                        "finite full-phase network and history-based legal control. It adds no " +
                        "hidden phase guards, costs or reference channels, and makes no claim " +
                        "about the cost of obtaining a complete behavior boundary."))),
            DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        return Disp(Every("N", Constant("Nat"), Every("m", Constant("Nat"),
            ImpliesBoth(
                Conjoin(Le(Num(2), Variable("N")), Le(Num(2), Variable("m"))),
                Witness("C", Constant("Network"),
                    Witness("iv", Call("Equiv", Vertices(), Call("Fin", Variable("N"))),
                        Witness("ie", Call("Equiv", Edges(), Call("Fin", Bound())),
                            Witness("root", Vertices(), Witness("last", Vertices(),
                                Conjoin(
                                    Equal(Field(Variable("C"), "m"), Variable("m")),
                                    Equal(Rank(Variable("root")), Num(0)),
                                    Equal(Rank(Variable("last")), Bound()),
                                    EdgeEquations(),
                                    PortEquations(),
                                    IterateEquations(),
                                    PathEquations(),
                                    PrefixEquations(),
                                    TerminalEquations(),
                                    SharpnessEquations(),
                                    Witness("trace", TraceType(), TraceEquations())))))))))));
    }

    private static Formula EdgeEquations()
    {
        Formula e = Variable("e");
        return Every("e", Edges(), Conjoin(
            Equal(Rank(Apply(Field(Variable("C"), "src"), e)), Value(Apply(Variable("ie"), e))),
            Equal(Rank(Apply(Field(Variable("C"), "dst"), e)), Add(Value(Apply(Variable("ie"), e)), Num(1))),
            Equal(Apply(Field(Variable("C"), "a"), e), Num(1)),
            Equal(Apply(Field(Variable("C"), "c"), e), PhaseNumeral(0))));
    }

    private static Formula PortEquations() => Every("v", Vertices(),
        Equal(Port(Variable("v")),
            Call("if", Equal(Rank(Variable("v")), Bound()), Variable("m"), Num(1))));

    private static Formula IterateEquations() => Every("n", Constant("Nat"),
        Every("v", Vertices(), Equal(Iterate(Variable("n"), Variable("v")),
            Call("if", Less(Add(Rank(Variable("v")), Variable("n")), Bound()), Num(1), Variable("m")))));

    private static Formula PathEquations() => Every("v", Vertices(), Every("w", Vertices(),
        Every("p", Path(Variable("v"), Variable("w")), Conjoin(
            Equal(Rank(Variable("w")), Add(Rank(Variable("v")), Length(Variable("p")))),
            Every("t", Phases(), Equal(Run(Variable("p"), Variable("t")), Variable("t")))))));

    private static Formula PrefixEquations() => Every("w", Vertices(),
        Every("p", Path(Variable("root"), Variable("w")),
            ImpliesBoth(Less(Length(Variable("p")), Bound()),
                Every("u", Vertices(), Every("r", Path(Variable("root"), Variable("u")),
                    Every("s", Path(Variable("u"), Variable("w")),
                        ImpliesBoth(Equal(Variable("p"), Apply(Field(Variable("r"), "comp"), Variable("s"))),
                            Conjoin(Equal(Port(Variable("u")), Num(1)),
                                Equal(Read(Variable("u"), Run(Variable("r"), PhaseNumeral(0))),
                                    Read(Variable("u"), Run(Variable("r"), PhaseNumeral(1))))))))))));

    private static Formula TerminalEquations() => Witness("p", Path(Variable("root"), Variable("last")),
        Conjoin(Equal(Length(Variable("p")), Bound()),
            Every("t", Phases(),
                Equal(Value(Read(Variable("last"), Run(Variable("p"), Variable("t")))), Value(Variable("t")))),
            NotEqual(Read(Variable("last"), Run(Variable("p"), PhaseNumeral(0))),
                Read(Variable("last"), Run(Variable("p"), PhaseNumeral(1))))));

    private static Formula SharpnessEquations() => Every("n", Constant("Nat"),
        ImpliesBoth(Less(Variable("n"), Bound()), Conjoin(
            Equal(Iterate(Variable("n"), Variable("root")), Num(1)),
            Equal(Iterate(Bound(), Variable("root")), Variable("m")),
            NotEqual(Iterate(Variable("n"), Variable("root")), Iterate(Bound(), Variable("root"))))));

    private static Formula TraceType() => Every("v", Vertices(), Every("w", Vertices(),
        Arrow(Path(Variable("v"), Variable("w")), Arrow(Phases(), Events()))));

    private static Formula Events() => Call("List", Call("Sum", Edges(),
        SigmaType("z", Vertices(), Call("ZMod", Port(Variable("z"))))));

    private static Formula TraceNilEquation() => Every("v", Vertices(), Every("t", Phases(),
        Equal(Trace(Nil(Variable("v")), Variable("t")),
            EventList(ReadEvent(Variable("v"), Read(Variable("v"), Variable("t")))))));

    private static Formula TraceConsEquation()
    {
        Formula p = Variable("p");
        Formula e = Variable("e");
        Formula t = Variable("t");
        Formula x = Variable("x");
        return Every("v", Vertices(), Every("w", Vertices(), Every("x", Vertices(),
            Every("p", Path(Variable("v"), Variable("w")),
                Every("e", Hom(Variable("w"), x), Every("t", Phases(),
                    Equal(Trace(Cons(p, e), t), Append(Trace(p, t),
                        EventList(Apply(Field(Constant("Sum"), "inl"), Projection(e, 1)),
                            ReadEvent(x, Read(x, Run(Cons(p, e), t))))))))))));
    }

    private static Formula TraceEquations() => Conjoin(
        TraceNilEquation(),
        TraceConsEquation(),
        Every("w", Vertices(), Every("p", Path(Variable("root"), Variable("w")),
            ImpliesBoth(Less(Length(Variable("p")), Bound()),
                Equal(Trace(Variable("p"), PhaseNumeral(0)), Trace(Variable("p"), PhaseNumeral(1)))))),
        Every("K", Call("Type", Constant("u")), Every("choose", ChooseType(),
            Witness("execute", ExecuteType(), ExecuteEquations()))));

    private static Formula ChooseType() => Every("v", Vertices(),
        Arrow(Variable("K"), Arrow(Events(), Call("Option", NextType(Variable("v"))))));

    private static Formula NextType(Formula v) => SigmaType("w", Vertices(),
        Call("Prod", Hom(v, Variable("w")), Variable("K")));

    private static Formula StateType() => Call("Prod",
        SigmaType("w", Vertices(), Path(Variable("root"), Variable("w"))), Variable("K"));

    private static Formula ExecuteType() => Arrow(Phases(),
        Arrow(Variable("K"), Arrow(Constant("Nat"), StateType())));

    private static Formula ExecuteEquations()
    {
        Formula t = Variable("t");
        Formula k = Variable("k");
        Formula n = Variable("n");
        Formula state0 = Execute(PhaseNumeral(0), k, n);
        Formula state1 = Execute(PhaseNumeral(1), k, n);
        return Conjoin(
            Every("t", Phases(), Every("k", Variable("K"),
                Equal(Execute(t, k, Num(0)), Pair(Pack(Variable("root"), Nil(Variable("root"))), k)))),
            Every("t", Phases(), Every("k", Variable("K"), Every("n", Constant("Nat"),
                Equal(Execute(t, k, Add(n, Num(1))), ExecuteStep(t, k, n))))),
            Every("t", Phases(), Every("k", Variable("K"), Every("n", Constant("Nat"),
                Le(Length(StatePath(Execute(t, k, n))), n)))),
            Every("k", Variable("K"), Every("n", Constant("Nat"),
                ImpliesBoth(Less(n, Bound()), Conjoin(
                    Equal(state0, state1),
                    Equal(Trace(StatePath(state0), PhaseNumeral(0)), Trace(StatePath(state1), PhaseNumeral(1))),
                    Call("HEq", Choice(state0, PhaseNumeral(0)), Choice(state1, PhaseNumeral(1))))))));
    }

    private static Formula ExecuteStep(Formula t, Formula k, Formula n)
    {
        Formula state = Variable("state");
        Formula next = Variable("next");
        Formula appended = Pair(
            Pack(Projection(next, 1), Cons(StatePath(state), Projection(Projection(next, 2), 1))),
            Projection(Projection(next, 2), 2));
        return Seq(Constant("let"), Sp, state, Colon, StateType(), Sp, Colon, Eq, Sp,
            Execute(t, k, n), Sp, Constant("in"), Sp,
            Constant("match"), Sp, Choice(state, t), Sp, Constant("with"), Sp,
            new Formula.Aligned([
                Seq(Bar, Sp, Constant("none"), Sp, Mapsto, Sp, state),
                Seq(Bar, Sp, Apply(Constant("some"), Typed(next, NextType(StateVertex(state)))),
                    Sp, Mapsto, Sp, appended)
            ]));
    }

    private static Formula TraceFormula() => Disp(Conjoin(TraceNilEquation(), TraceConsEquation()));

    private static Formula Variable(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Constant(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Every(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Witness(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula ImpliesBoth(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[clauses.Length - 1];
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Parentheses(Formula value) => Seq(Open, value, Close);
    private static Formula Field(Formula value, string name) => Seq(Parentheses(value), Dot, Constant(name));
    private static Formula Projection(Formula value, byte index) => Seq(Parentheses(value), Dot, D(index));
    private static Formula Typed(Formula value, Formula type) => Parentheses(Seq(value, Colon, type));
    private static Formula SigmaType(string name, Formula domain, Formula body) =>
        Parentheses(Seq(Sigma, Sp, Variable(name), Colon, domain, Comma, Sp, body));
    private static Formula Pack(Formula first, Formula second) => Seq(Langle, Sp, first, Comma, second, Rangle);
    private static Formula Pair(Formula first, Formula second) => Parentheses(Seq(first, Comma, second));
    private static Formula EventList(Formula first) => Seq(OpenBracket, first, CloseBracket);
    private static Formula EventList(Formula first, Formula second) => Seq(OpenBracket, first, Comma, second, CloseBracket);
    private static Formula Append(Formula first, Formula second) => Seq(Parentheses(first), Plus, Plus, second);
    private static Formula Vertices() => Field(Variable("C"), "V");
    private static Formula Edges() => Field(Variable("C"), "E");
    private static Formula Bound() => Subtract(Variable("N"), Num(1));
    private static Formula Phases() => Call("ZMod", Field(Variable("C"), "m"));
    private static Formula PhaseNumeral(long value) => Typed(Num(value), Phases());
    private static Formula Value(Formula value) => Field(value, "val");
    private static Formula Rank(Formula v) => Value(Apply(Variable("iv"), v));
    private static Formula Port(Formula v) => Apply(Field(Variable("C"), "d"), v);
    private static Formula Iterate(Formula n, Formula v) => Call("iterate", Variable("C"), n, v);
    private static Formula Path(Formula v, Formula w) => Call("NPath", Variable("C"), v, w);
    private static Formula Hom(Formula v, Formula w) => Apply(Field(Call("networkQuiver", Variable("C")), "Hom"), v, w);
    private static Formula Length(Formula p) => Field(p, "length");
    private static Formula Nil(Formula v) => Typed(Field(Constant("Path"), "nil"), Path(v, v));
    private static Formula Cons(Formula p, Formula e) => Apply(Field(p, "cons"), e);
    private static Formula Run(Formula p, Formula t) => Call("pathRun", p, t);
    private static Formula Read(Formula v, Formula t) => Call("portRead", Variable("C"), v, t);
    private static Formula ReadEvent(Formula v, Formula value) => Apply(Field(Constant("Sum"), "inr"), Pack(v, value));
    private static Formula Trace(Formula p, Formula t) => Apply(Variable("trace"), p, t);
    private static Formula Execute(Formula t, Formula k, Formula n) => Apply(Variable("execute"), t, k, n);
    private static Formula StateVertex(Formula state) => Projection(Projection(state, 1), 1);
    private static Formula StatePath(Formula state) => Projection(Projection(state, 1), 2);
    private static Formula Choice(Formula state, Formula t) => Apply(Variable("choose"),
        StateVertex(state), Projection(state, 2), Trace(StatePath(state), t));
}

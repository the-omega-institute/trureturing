using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class AcceptedWordEffectPropagationDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula n, Formula q) =>
        Call("propagation", V("M"), V("F"), V("A"), V("U"), n, q);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, V(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula N => V("N");
    private static Formula Bot => Call("bottom");
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Call("ite", condition, yes, no);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual accepted partial runs generate effect propagation, a simultaneous finite horizon, and arbitrary initial-state delay.",
        H("Accepted words and legal future effects"),
        Blocks(
            Paragraph(Text("Let K be a division ring and E a left K-module with an additive commutative group. "
                + "Let Alphabet and Q be arbitrary types, with decidable equality on Q. A BaseAutomaton M "
                + "has a distinguished start state and partial transition M.step(q,a). Its existing runFrom "
                + "operation follows the list from left to right, returning none as soon as a transition is absent. "
                + "Let F be a finite set of accepting states, A assign a total K-linear endomorphism to each letter, "
                + "and U be the common terminal submodule. No epsilon transitions or intermediate reads are added. "
                + "For chronological w = a1...ak the effect is the list product A(a1)...A(ak): the head acts after "
                + "the tail and the empty word acts as identity. Real finite-dimensional spaces are obtained by K = R.")),
            Def("acceptance", "Accepts", "Actual terminal acceptance",
                Acceptance(Eqn(Call("Accepts", V("M"), V("F"), V("q"), V("w")),
                    Seq(Exists, Sp, V("f"), Sp, InMacro, Sp, V("F"), Comma, Sp,
                        Eqn(Call("runFrom", V("M"), V("q"), V("w")), Call("some", V("f")))))),
                "Acceptance requires a successful whole run ending in F. A missing transition supplies no execution event."),
            Def("accepted-span", "acceptedSpan", "Bounded accepted effect span",
                General(All("n", N, All("q", V("Q"),
                    Eqn(Call("acceptedSpan", V("M"), V("F"), V("A"), V("U"), V("n"), V("q")),
                        WordSpan(true)))), decidable: false),
                "The span is defined directly from runFrom acceptance and word length, independently of the recurrence."),
            Def("full-future", "fullFuture", "All finite accepted effects",
                General(All("q", V("Q"),
                    Eqn(Call("fullFuture", V("M"), V("F"), V("A"), V("U"), V("q")),
                        WordSpan(false))), decidable: false),
                "There is no length bound. Only accepted terminal reads contribute."),
            Def("effect-step", "effectStep", "One propagation step",
                General(All("S", Seq(V("Q"), Sp, To, Sp, Call("Submodule", V("K"), V("E"))),
                    All("q", V("Q"), Eqn(Call("effectStep", V("M"), V("A"), V("S"), V("q")),
                    Add(Call("apply", V("S"), V("q")),
                        Call("sup", Seq(V("a"), Comma, Sp, V("qprime"), Comma, Sp,
                            Eqn(Call("step", V("M"), V("q"), V("a")), Call("some", V("qprime")))),
                            Call("map", Call("apply", V("S"), V("qprime")), Call("apply", V("A"), V("a")))))))),
                    decidable: false, final: false, seed: false),
                "The supremum is the sum of the image subspaces indexed by all and only defined transitions. "
                    + "Repeated targets and loops are allowed. An empty index family contributes the zero submodule."),
            Def("propagation", "propagation", "The all-state recurrence",
                General(Seq(
                    All("q", V("Q"), Eqn(P(D(0), V("q")),
                        If(Seq(V("q"), Sp, InMacro, Sp, V("F")), V("U"), Bot))),
                    Sp, Land, Sp,
                    All("n", N, All("q", V("Q"), Eqn(P(Add(V("n"), D(1)), V("q")),
                        Call("effectStep", V("M"), V("A"),
                            Call("propagation", V("M"), V("F"), V("A"), V("U"), V("n")), V("q"))))))),
                "The initialization is U exactly at accepting states and zero elsewhere. The next tuple uses the same "
                    + "fixed transition operator, so a simultaneous plateau is a fixed point."),
            Thm("word-characterization", "propagation_eq_accepted", "Exact accepted-word characterization",
                General(All("n", N, All("q", V("Q"), Eqn(P(V("n"), V("q")),
                    Call("acceptedSpan", V("M"), V("F"), V("A"), V("U"), V("n"), V("q")))))),
                "At horizon zero the only possible word is empty. A nonempty accepted word uniquely separates "
                    + "into its head a, the actual next state qprime, and an accepted tail from qprime. "
                    + "The identity A(aw) = A(a)A(w), submodule map of a span, and induction identify the independent "
                    + "word span with the recurrence at every state and horizon. No extra permission or read is inferred."),
            Thm("simultaneous-stabilization", "simultaneous_stabilization", "The simultaneous rank-offset horizon",
                General(Stabilization(), true),
                "Assume Q is finite and E is finite dimensional. Set d = finrank(K,E), r = finrank(K,U), "
                    + "and B = |Q|d - |F|r, using natural subtraction. The rank sum over the actual coordinate "
                    + "subspaces starts at |F|r and is bounded by |Q|d. The existing "
                    + "FiniteSequentialWordCertificate.bounded_monotone_has_equal_step supplies a consecutive "
                    + "equal-rank pair by B. Since every coordinate increases, equality of the sums forces "
                    + "equal rank at every coordinate; inclusion then forces simultaneous subspace equality. "
                    + "Iteration of the same tuple operator preserves that equality. Every accepted word belongs "
                    + "to its own finite-horizon span, hence to the stable tuple, proving fullFuture(q) = propagation(B,q) "
                    + "for every q, including the distinguished start. This uses the sum of coordinate ranks directly; "
                    + "it does not identify that sum with the rank of a correlated lifted space. Empty F or Alphabet, "
                    + "zero U or E, arbitrary loops and partial undefined transitions need no additional hypothesis."),
            Def("chain", "chain", "The actual finite successor chain",
                Disp(All("L", N, Seq(Eqn(Call("start", Call("chain", V("L"))), D(0)), Sp, Land, Sp,
                    All("q", Call("Fin", Add(V("L"), D(1))),
                        Eqn(Call("step", Call("chain", V("L")), V("q"), Call("unit")),
                            If(Seq(Call("val", V("q")), Sp, Lt, Sp, V("L")),
                                Call("some", Add(Call("val", V("q")), D(1))), Call("none"))))))),
                "The alphabet is Unit, the states are Fin(L+1), the start has value zero, and only the final state "
                    + "has no successor. The displayed natural successor is regarded as its bounded Fin element."),
            Def("chain-final", "chainFinal", "Sole terminal acceptance",
                Disp(All("L", N, Eqn(Call("chainFinal", V("L")), Seq(OpenBrace, V("L"), CloseBrace)))),
                "The singleton contains the Fin(L+1) state of value L. It also describes the length-zero chain."),
            Thm("arbitrary-delay", "arbitrary_chain_delay", "Arbitrary initial-state plateaus",
                ChainDelay(),
                "For every natural L and every submodule U over any of the stated scalar and carrier choices, "
                    + "put every letter effect equal to identity and accept only the chain terminal. At state q "
                    + "the propagated space is U exactly when L <= q.val+n and is zero otherwise. Induction on n "
                    + "uses the actual successor edge and the absence of an edge from the terminal. Consequently "
                    + "the initial space is zero for every n<L and is U at L. Taking K=R, E=R and U=R gives "
                    + "the scalar delay family, with L=0 and L=1 included. If L>=2 and U is nonzero, the "
                    + "initial spaces at zero and one agree, but the length-L space differs. Thus equality at the "
                    + "initial state alone cannot replace simultaneous equality. Arbitrarily many initial plateaus "
                    + "follow by increasing L. These are algebraic horizon statements; they assert no numerical, "
                    + "physical-resource or cost improvement."))));

    private static DocumentBlock.Describe Def(string id, string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Root + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Root + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula Acceptance(Formula body) => Disp(Seq(Forall, Sp, V("Alphabet"), Comma,
        Sp, V("Q"), Colon, Sp, V("Type"), Comma, Sp,
        All("M", Call("BaseAutomaton", V("Alphabet"), V("Q")),
            All("F", Call("Finset", V("Q")), All("q", V("Q"),
                All("w", Call("List", V("Alphabet")), body))))));

    private static Formula General(Formula body, bool finite = false, bool decidable = true,
        bool final = true, bool seed = true)
    {
        var xs = new List<Formula> { Forall, Sp, V("K"), Comma, Sp, V("E"), Comma, Sp,
            V("Alphabet"), Comma, Sp, V("Q"), Colon, Sp, V("Type"), Comma, Sp,
            OpenBracket, Call("DivisionRing", V("K")), CloseBracket, Sp,
            OpenBracket, Call("AddCommGroup", V("E")), CloseBracket, Sp,
            OpenBracket, Call("Module", V("K"), V("E")), CloseBracket, Sp };
        if (decidable) xs.AddRange([OpenBracket, Call("DecidableEq", V("Q")), CloseBracket, Sp]);
        if (finite) xs.AddRange([OpenBracket, Call("Fintype", V("Q")), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", V("K"), V("E")), CloseBracket, Sp]);
        xs.AddRange([Forall, Sp, V("M"), Colon, Sp, Call("BaseAutomaton", V("Alphabet"), V("Q")), Comma, Sp]);
        if (final) xs.AddRange([V("F"), Colon, Sp, Call("Finset", V("Q")), Comma, Sp]);
        xs.AddRange([V("A"), Colon, Sp, V("Alphabet"), Sp, To, Sp, Call("End", V("K"), V("E")), Comma, Sp]);
        if (seed) xs.AddRange([V("U"), Colon, Sp, Call("Submodule", V("K"), V("E")), Comma, Sp]);
        xs.Add(body);
        return Disp(Seq([.. xs]));
    }

    private static Formula WordSpan(bool bounded)
    {
        var xs = new List<Formula> { OpenBrace, V("x"), Sp, Mid, Sp, Exists, Sp, V("w"), Colon,
            Sp, Call("List", V("Alphabet")), Comma, Sp };
        if (bounded) xs.AddRange([Call("length", V("w")), Sp, Leq, Sp, V("n"), Sp, Land, Sp]);
        xs.AddRange([Call("Accepts", V("M"), V("F"), V("q"), V("w")), Sp, Land, Sp,
            Exists, Sp, V("t"), Sp, InMacro, Sp, V("U"), Comma, Sp,
            Eqn(V("x"), Call("apply", Call("prod", Call("map", V("A"), V("w"))), V("t"))), CloseBrace]);
        return Call("span", V("K"), Seq([.. xs]));
    }

    private static Formula Stabilization()
    {
        Formula b = Seq(Call("card", V("Q")), Sp, Times, Sp, Call("finrank", V("K"), V("E")),
            Sp, Minus, Sp, Call("card", V("F")), Sp, Times, Sp, Call("finrank", V("K"), V("U")));
        Formula flat = All("q", V("Q"), Eqn(P(Add(V("n"), D(1)), V("q")), P(V("n"), V("q"))));
        Formula permanent = All("n", N, Seq(Open, flat, Close, Sp, Rightarrow, Sp,
            All("m", N, All("q", V("Q"), Eqn(P(Add(V("n"), V("m")), V("q")), P(V("n"), V("q")))))));
        Formula stable = All("n", N, Seq(b, Sp, Leq, Sp, V("n"), Sp, Rightarrow, Sp,
            All("q", V("Q"), Eqn(P(V("n"), V("q")), P(b, V("q"))))));
        Formula full = All("q", V("Q"), Eqn(Call("fullFuture", V("M"), V("F"), V("A"), V("U"), V("q")), P(b, V("q"))));
        return Seq(Open, permanent, Close, Sp, Land, Sp, Open, stable, Close, Sp, Land, Sp, full);
    }

    private static Formula ChainDelay()
    {
        Formula c = Call("chain", V("L")), f = Call("chainFinal", V("L"));
        Formula C(Formula n, Formula q) => Call("propagation", c, f, Call("constantIdentity"), V("U"), n, q);
        Formula start = Call("start", c);
        Formula all = All("n", N, All("q", Call("Fin", Add(V("L"), D(1))),
            Eqn(C(V("n"), V("q")), If(Seq(V("L"), Sp, Leq, Sp, Add(Call("val", V("q")), V("n"))), V("U"), Bot))));
        Formula earlier = All("n", N, Seq(V("n"), Sp, Lt, Sp, V("L"), Sp, Rightarrow, Sp, Eqn(C(V("n"), start), Bot)));
        Formula plateau = Seq(D(2), Sp, Leq, Sp, V("L"), Sp, Rightarrow, Sp, V("U"), Sp, Neq, Sp, Bot,
            Sp, Rightarrow, Sp, Open, Eqn(C(D(1), start), C(D(0), start)), Sp, Land, Sp,
            C(V("L"), start), Sp, Neq, Sp, C(D(0), start), Close);
        return Disp(Seq(Forall, Sp, V("K"), Comma, Sp, V("E"), Colon, Sp, V("Type"), Comma, Sp,
            OpenBracket, Call("DivisionRing", V("K")), CloseBracket, Sp,
            OpenBracket, Call("AddCommGroup", V("E")), CloseBracket, Sp,
            OpenBracket, Call("Module", V("K"), V("E")), CloseBracket, Sp,
            All("L", N, All("U", Call("Submodule", V("K"), V("E")), Seq(Open, all, Close, Sp, Land, Sp,
                Open, earlier, Close, Sp, Land, Sp, Eqn(C(V("L"), start), V("U")), Sp, Land, Sp, plateau)))));
    }

    private static Formula Call(string name, params Formula[] args)
    {
        var xs = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) xs.AddRange([Comma, Sp]);
            xs.Add(args[i]);
        }
        xs.Add(Close);
        return Seq([.. xs]);
    }
}

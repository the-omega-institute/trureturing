using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class ActionGraphCommunicationBoundDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.";
    private const string RunWordOwner =
        "D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cumulative cost on a finite deterministic action graph is bounded exactly when every closed action word has zero cost.",
        H("Action Graph Communication Bound"),
        Blocks(
            EntryAt(
                "action-word-run",
                RunWordOwner,
                "runWord",
                "Finite action words determine terminal states",
                RunFormula(),
                "Starting at m, the empty word leaves the state unchanged. Executing a word whose first action is f first applies the deterministic transition T_f and then executes the remaining word.",
                DescribeRole.Definition),
            Entry(
                "finite-word-communication",
                "Comm",
                "Finite-word communication is the sum of step costs",
                CommFormula(),
                "The empty word costs zero. A nonempty word pays the cost of its first labelled edge and then pays the cost of the remaining execution from the successor state.",
                DescribeRole.Definition),
            Entry(
                "infinite-word-communication",
                "InfiniteComm",
                "Infinite-word communication is a prefix supremum",
                InfiniteCommFormula(),
                "The total cost of an infinite action word is the supremum in the extended natural numbers of the costs of all its finite prefixes.",
                DescribeRole.Definition),
            Entry(
                "maximal-edge-cost",
                "maxEdgeCost",
                "The finite supremum of edge costs",
                MaxEdgeCostFormula(),
                "For finite state and action carriers, W_max is the finite supremum of all labelled-edge costs; its value is zero if either carrier is empty.",
                DescribeRole.Definition),
            Entry(
                "cumulative-communication-criterion",
                "cumulative_communication_criterion",
                "Cumulative communication criterion",
                CriterionFormula(),
                "Let Q and the action alphabet be finite and nonempty. Let I be a set of initial states, and assume every state is reached from I by some finite action word; since the state type is nonempty, I is then nonempty. Then finite total cost for every infinite execution, one common bound for all finite executions from I, and zero cost for every nonempty closed action word are equivalent.",
                DescribeRole.Theorem,
                "If the cycle condition holds, remove a closed segment whenever an execution repeats a state. The segment has zero cost and its deletion preserves the state from which the suffix runs. Iteration leaves a path with no repeated state, hence at most card(Q)-1 edges, and each edge costs at most W_max.",
                "Conversely, a reachable positive-cost cycle can be repeated after a prefix leading to it. Determinism returns to the same state after each copy, so its prefix costs are unbounded. A common finite-word bound directly bounds every infinite-word prefix supremum."))));

    private static DocumentBlock Entry(
        string id,
        string selector,
        string title,
        Formula formula,
        string first,
        DescribeRole role,
        params string[] rest) =>
        EntryAt(id, Owner, selector, title, formula, first, role, rest);

    private static DocumentBlock EntryAt(
        string id,
        string owner,
        string selector,
        string title,
        Formula formula,
        string first,
        DescribeRole role,
        params string[] rest)
    {
        var paragraphs = new List<DocumentBlock> { Paragraph(Text(first)) };
        paragraphs.AddRange(rest.Select(text => Paragraph(Text(text))));
        return Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(owner + selector),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(paragraphs.ToArray()),
            role);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Sp, type, CloseBracket);

    private static Formula SetOf(Formula type) => Call("Set", type);

    private static Formula ListOf(Formula type) => Call("List", type);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula ENat => Seq(Operatorname, Grp(F.Id("ENat")));

    private static Formula Action => Seq(Mathcal, Grp(F.Id("F")));

    private static Formula State => F.Id("Q");

    private static Formula RunWord(Formula word, Formula state) =>
        Call("runWord", F.Id("T"), word, state);

    private static Formula Cost(Formula state, Formula word) =>
        Call("Comm", F.Id("T"), F.Id("w"), state, word);

    private static Formula RunFormula()
    {
        Formula state = F.Id("m");
        Formula action = F.Id("f");
        Formula word = F.Id("u");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, State, Comma, Sp, Action, Comma, Sp,
            F.Id("T"), Colon, Sp,
            new Formula.TypeArrow(Action, new Formula.TypeArrow(State, State)),
            Comma, RowBreak, Grp(),
            Forall, Sp, state, InMacro, Sp, State, Comma, Sp,
            RunWord(Seq(OpenBracket, CloseBracket), state), Sp, Eq, Sp, state,
            Comma, RowBreak, Grp(),
            Forall, Sp, action, InMacro, Sp, Action, Comma, Sp,
            Forall, Sp, word, InMacro, Sp, ListOf(Action), Comma, Sp,
            RunWord(Call("cons", action, word), state), Sp, Eq, Sp,
            RunWord(word, Call("T", action, state)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CommFormula()
    {
        Formula state = F.Id("m");
        Formula action = F.Id("f");
        Formula word = F.Id("u");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, State, Comma, Sp, Action, Comma, Sp,
            F.Id("T"), Colon, Sp,
            new Formula.TypeArrow(Action, new Formula.TypeArrow(State, State)),
            Comma, Sp,
            F.Id("w"), Colon, Sp,
            new Formula.TypeArrow(State, new Formula.TypeArrow(Action, Nat)),
            Comma, RowBreak, Grp(),
            Forall, Sp, state, InMacro, Sp, State, Comma, Sp,
            Cost(state, Seq(OpenBracket, CloseBracket)), Sp, Eq, Sp, D(0),
            Comma, RowBreak, Grp(),
            Forall, Sp, action, InMacro, Sp, Action, Comma, Sp,
            Forall, Sp, word, InMacro, Sp, ListOf(Action), Comma, Sp,
            Cost(state, Call("cons", action, word)), Sp, Eq, Sp,
            Call("w", state, action), Sp, Plus, Sp,
            Cost(Call("T", action, state), word), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula InfiniteCommFormula()
    {
        Formula state = F.Id("m");
        Formula omega = Omega;
        Formula n = F.Id("n");
        return Disp(Seq(
            Forall, Sp, State, Comma, Sp, Action, Comma, Sp,
            F.Id("T"), Colon, Sp,
            new Formula.TypeArrow(Action, new Formula.TypeArrow(State, State)),
            Comma, Sp,
            F.Id("w"), Colon, Sp,
            new Formula.TypeArrow(State, new Formula.TypeArrow(Action, Nat)),
            Comma, RowBreak,
            Forall, Sp, state, InMacro, Sp, State, Comma, Sp,
            Forall, Sp, omega, Colon, Sp,
            new Formula.TypeArrow(Nat, Action), Comma, RowBreak,
            Call("InfiniteComm", F.Id("T"), F.Id("w"), state, omega), Sp,
            Eq, Sp, Operatorname, Grp(F.Id("sup")), Underscore, Grp(n, Ge, D(0)), Sp,
            Cost(state, Call("prefix", omega, n)), Sp, InMacro, Sp, ENat, Dot));
    }

    private static Formula MaxEdgeCostFormula()
    {
        Formula state = F.Id("m");
        Formula action = F.Id("f");
        return Disp(Seq(
            Forall, Sp, State, Comma, Sp, Action, Comma, Sp,
            Typeclass("Fintype", State), Comma, Sp,
            Typeclass("Fintype", Action), Comma, Sp,
            F.Id("w"), Colon, Sp,
            new Formula.TypeArrow(State, new Formula.TypeArrow(Action, Nat)),
            Comma, RowBreak,
            Call("maxEdgeCost", F.Id("w")), Sp, Eq, Sp,
            Operatorname, Grp(F.Id("sup")), Underscore, Grp(state, InMacro, Sp, State, Comma, Sp,
                action, InMacro, Sp, Action), Sp,
            Call("w", state, action), Dot));
    }

    private static Formula CriterionFormula()
    {
        Formula state = F.Id("m");
        Formula initial = Seq(F.Id("m"), Underscore, Grp(D(0)));
        Formula action = F.Id("f");
        Formula prefix = F.Id("p");
        Formula finiteWord = F.Id("u");
        Formula cycle = F.Id("v");
        Formula omega = Omega;
        Formula bound = F.Id("B");
        Formula initialSet = F.Id("I");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula wmax = Seq(F.Id("W"), Underscore, Grp(F.Id("max")));

        Formula reachable = Seq(
            Forall, Sp, state, InMacro, Sp, State, Comma, Sp,
            Exists, Sp, initial, InMacro, Sp, initialSet, Comma, Sp,
            Exists, Sp, prefix, InMacro, Sp, ListOf(Action), Comma, Sp,
            RunWord(prefix, initial), Sp, Eq, Sp, state);
        Formula finiteInfinite = Seq(
            a, Colon, Sp,
            Forall, Sp, initial, InMacro, Sp, initialSet, Comma, Sp,
            Forall, Sp, omega, Colon, Sp,
            new Formula.TypeArrow(Nat, Action), Comma, Sp,
            Call("InfiniteComm", F.Id("T"), F.Id("w"), initial, omega), Sp,
            Neq, Sp, Infty);
        Formula uniformlyBounded = Seq(
            b, Colon, Sp,
            Exists, Sp, bound, InMacro, Sp, Nat, Comma, Sp,
            Forall, Sp, initial, InMacro, Sp, initialSet, Comma, Sp,
            Forall, Sp, finiteWord, InMacro, Sp, ListOf(Action), Comma, Sp,
            Cost(initial, finiteWord), Sp, Leq, Sp, bound);
        Formula zeroCycles = Seq(
            c, Colon, Sp,
            Forall, Sp, state, InMacro, Sp, State, Comma, Sp,
            Forall, Sp, cycle, InMacro, Sp, ListOf(Action), Comma, Sp,
            cycle, Sp, Neq, Sp, Seq(OpenBracket, CloseBracket), Sp, Land, Sp,
            RunWord(cycle, state), Sp, Eq, Sp, state, Sp, Rightarrow, Sp,
            Cost(state, cycle), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, State, Comma, Sp, Action, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Fintype", State), Comma, Sp,
            Typeclass("Nonempty", State), Comma, RowBreak, Grp(),
            Typeclass("Fintype", Action), Comma, Sp,
            Typeclass("Nonempty", Action), Comma, Sp,
            initialSet, Colon, Sp, SetOf(State), Comma, RowBreak,
            F.Id("T"), Colon, Sp,
            new Formula.TypeArrow(Action, new Formula.TypeArrow(State, State)),
            Comma, Sp,
            F.Id("w"), Colon, Sp,
            new Formula.TypeArrow(State, new Formula.TypeArrow(Action, Nat)),
            Comma, RowBreak,
            reachable, Comma, RowBreak,
            wmax, Sp, Eq, Sp, Call("maxEdgeCost", F.Id("w")), Comma, RowBreak,
            finiteInfinite, Comma, RowBreak,
            uniformlyBounded, Comma, RowBreak,
            zeroCycles, Comma, RowBreak,
            Operatorname, Grp(F.Id("List"), Dot, F.Id("TFAE")), Open,
            OpenBracket, a, Comma, Sp, b, Comma, Sp, c, CloseBracket, Close,
            Sp, Land, RowBreak,
            Open, c, Sp, Rightarrow, Sp,
            Forall, Sp, initial, InMacro, Sp, initialSet, Comma, Sp,
            Forall, Sp, finiteWord, InMacro, Sp, ListOf(Action), Comma, Sp,
            Cost(initial, finiteWord), Sp, Leq, Sp,
            Open, Call("card", State), Sp, Minus, Sp, D(1), Close,
            Sp, wmax, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

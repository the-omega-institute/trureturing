using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ArchiveClockRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite synchronized executions characterize archive-clock recovery and bound its first ambiguity.",
        H("Archive Clock Recovery"),
        Blocks(
            Def(
                "archive-clock-system",
                "System",
                "Finite partial-action systems",
                SystemFormula(),
                "A system assigns to each action a decidable domain, a total successor and integer cost, "
                    + "and a reading defined only on that action's domain. Values outside the domain "
                    + "never enter a legal execution, so this preserves the source partial-map model, "
                    + "including empty reading types and empty domains."),
            Def(
                "archive-clock-state-after",
                "stateAfter",
                "State after an action word",
                StateAfterFormula(),
                "The state after the empty word is the initial state. For a nonempty word, the "
                    + "first action changes the state and the remaining actions are then evaluated."),
            Def(
                "archive-clock-legal",
                "Legal",
                "Legal executions",
                LegalFormula(),
                "The empty execution is legal. A nonempty execution is legal exactly when its first "
                    + "action is defined at the current state and its tail is legal from the successor."),
            Def(
                "archive-clock-visible-archive",
                "visibleArchive",
                "Visible archives",
                VisibleArchiveFormula(),
                "Each execution step records the chosen action together with the reading produced at "
                    + "the state where that action is taken."),
            Def(
                "archive-clock-clock",
                "clock",
                "Accumulated clock",
                ClockFormula(),
                "The clock of an execution is the sum of the integer costs of its actions at their "
                    + "successive source states."),
            Def(
                "archive-clock-synchronized-edge",
                "SynchronizedEdge",
                "Synchronized edges",
                SynchronizedEdgeFormula(),
                "A synchronized edge applies one action legally to two states and requires the two "
                    + "visible readings for that action to agree."),
            Def(
                "archive-clock-synchronized-path",
                "SynchronizedPath",
                "Synchronized paths",
                SynchronizedPathFormula(),
                "A synchronized path follows the same action word from two states, with a synchronized "
                    + "edge at every step."),
            Def(
                "archive-clock-pair-trace",
                "pairTrace",
                "Synchronized pair traces",
                PairTraceFormula(),
                "The pair trace contains the initial state pair and every successive pair reached by "
                    + "the common action word."),
            Def(
                "archive-clock-delta-sum",
                "deltaSum",
                "Clock-difference sums",
                DeltaSumFormula(),
                "The delta sum accumulates, edge by edge, the first execution's cost minus the second "
                    + "execution's cost."),
            Def(
                "archive-clock-synchronous-reachability",
                "SynchronouslyReachable",
                "Synchronous reachability",
                SynchronouslyReachableFormula(),
                "A pair is synchronously reachable when a common synchronized word carries two allowed "
                    + "initial states to that pair."),
            Def(
                "archive-clock-recoverable",
                "ArchiveRecoverable",
                "Recovery from visible archives",
                ArchiveRecoverableFormula(),
                "Archive recoverability means that one integer-valued function of the visible archive "
                    + "equals the clock on every legal execution from every allowed initial state."),
            Describe.Lean(
                DescribeId.Create("archive-clock-recovery-and-finite-ambiguity"),
                DeclarationHandle.Create(Module + "archive_clock_recovery_and_finite_ambiguity"),
                H("Archive recovery is equivalent to synchronized cost consistency"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite configuration, action, and reading types, with n configurations "
                            + "and a nonempty allowed initial set, three conditions are equivalent: a "
                            + "single archive decoder recovers every legal clock, every synchronized "
                            + "path from allowed initial states has zero delta sum, and every synchronized "
                            + "edge whose source pair is synchronously reachable has zero cost difference.")),
                    Paragraph(Text(
                        "Two synchronized executions have the same visible archive, and their delta sum "
                            + "is exactly the difference of their clocks. Conversely, equality of visible "
                            + "archives synchronizes the two executions. Prefix subtraction turns zero "
                            + "path sums into zero reachable-edge differences.")),
                    Paragraph(Text(
                        "If recovery fails, choose a shortest synchronized word reaching the source of a "
                            + "nonzero edge. A repeated state pair would allow the intervening loop to be "
                            + "removed while preserving legality, readings, and the endpoint, contradicting "
                            + "minimality. Thus its pair trace has at most n squared vertices. According to "
                            + "whether the prefix delta is already nonzero, the prefix or the prefix followed "
                            + "by the bad edge gives equal archives, unequal clocks, and common length at most "
                            + "n squared."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(
        string id,
        string selector,
        string title,
        Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + selector),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Id(string name) => F.Id(name);

    private static Formula Lambda(string name, Formula body) =>
        Seq(F.LambdaLower, Sp, Id(name), Sp, F.Mapsto, Sp, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. arguments]);

    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula left, Formula right) => Call("pair", left, right);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula SetOf(Formula value) => Call("Set", value);
    private static Formula Product(Formula left, Formula right) => Call("Prod", left, right);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Paren(left), Sp, Land, Sp, Paren(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(Paren(left), Sp, Iff, Sp, Paren(right));
    private static Formula Implies(Formula left, Formula right) =>
        Seq(Paren(left), Sp, Rightarrow, Sp, Paren(right));

    private static Formula Types => Id("Type");
    private static Formula Naturals => Seq(Mathbb, Grp(Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(Id("Z")));
    private static Formula X => Id("X");
    private static Formula A => Id("A");
    private static Formula Y => Id("Y");
    private static Formula S => Id("S");
    private static Formula x => Id("x");
    private static Formula xp => Seq(Id("x"), Apos);
    private static Formula a => Id("a");
    private static Formula w => Id("w");
    private static Formula emptyWord => Seq(OpenBracket, CloseBracket);
    private static Formula wordType => ListOf(A);
    private static Formula archiveType => ListOf(Product(A, Y));

    private static Formula CommonParameters() => Seq(
        Forall, Sp, X, Comma, Sp, A, Comma, Sp, Y, Colon, Sp, Types, Comma, Sp,
        Forall, Sp, S, Colon, Sp, Call("System", X, A, Y), Comma, Sp);

    private static Formula SystemFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, X, Comma, Sp, A, Comma, Sp, Y, Colon, Sp, Types, Comma),
        Seq(Call("System", X, A, Y), Sp, Eq, Sp, OpenBrace,
            Id("D"), Colon, Sp, Arrow(A, Arrow(X, Id("Prop"))), Comma, Sp,
            Id("F"), Colon, Sp, Arrow(A, Arrow(X, X)), Comma, RowBreak, Grp(),
            Id("ell"), Colon, Sp,
                Forall, Sp, a, Colon, Sp, A, Comma, Sp,
                Forall, Sp, x, Colon, Sp, X, Comma, Sp,
                Arrow(Call("D", a, x), Y), Comma, Sp,
            Id("c"), Colon, Sp, Arrow(A, Arrow(X, Integers)), Comma, RowBreak, Grp(),
            Forall, Sp, a, Comma, Sp, x, Comma, Sp, Call("Decidable", Call("D", a, x)),
            CloseBrace, Dot),
    ]));

    private static Formula StateAfterFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, x, Colon, Sp, X, Comma),
        Seq(Equal(Call("stateAfter", S, x, emptyWord), x), Comma),
        Seq(Forall, Sp, a, Colon, Sp, A, Comma, Sp, Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
            Equal(Call("stateAfter", S, x, Call("cons", a, w)),
                Call("stateAfter", S, Call("successor", S, a, x), w)), Dot),
    ]));

    private static Formula LegalFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, x, Colon, Sp, X, Comma),
        Seq(Call("Legal", S, x, emptyWord), Comma),
        Seq(Forall, Sp, a, Colon, Sp, A, Comma, Sp, Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
            IffFormula(Call("Legal", S, x, Call("cons", a, w)),
                And(Call("domain", S, a, x),
                    Call("Legal", S, Call("successor", S, a, x), w))), Dot),
    ]));

    private static Formula VisibleArchiveFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, x, Colon, Sp, X, Comma),
        Seq(Equal(Call("visibleArchive", S, x, emptyWord), Seq(OpenBracket, CloseBracket)), Comma),
        Seq(Forall, Sp, a, Colon, Sp, A, Comma, Sp, Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
            Equal(Call("visibleArchive", S, x, Call("cons", a, w)),
                Call("dite", Call("domain", S, a, x),
                    Lambda("h", Call("cons",
                        Pair(a, Call("reading", S, a, x, Id("h"))),
                        Call("visibleArchive", S, Call("successor", S, a, x), w))),
                    Lambda("h", emptyWord))), Dot),
    ]));

    private static Formula ClockFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, x, Colon, Sp, X, Comma),
        Seq(Equal(Call("clock", S, x, emptyWord), D(0)), Comma),
        Seq(Forall, Sp, a, Colon, Sp, A, Comma, Sp, Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
            Equal(Call("clock", S, x, Call("cons", a, w)),
                Seq(Call("cost", S, a, x), Sp, Plus, Sp,
                    Call("clock", S, Call("successor", S, a, x), w))), Dot),
    ]));

    private static Formula SynchronizedEdgeFormula() => Disp(Seq(
        CommonParameters(), Forall, Sp, Id("p"), Colon, Sp, Product(X, X), Comma, Sp,
        Forall, Sp, a, Colon, Sp, A, Comma, Sp,
        IffFormula(
            Call("SynchronizedEdge", S, Id("p"), a),
            Seq(Exists, Sp, Id("h"), Colon, Sp,
                Call("domain", S, a, Call("fst", Id("p"))), Comma, Sp,
                Exists, Sp, Seq(Id("h"), Apos), Colon, Sp,
                    Call("domain", S, a, Call("snd", Id("p"))), Comma, Sp,
                Equal(Call("reading", S, a, Call("fst", Id("p")), Id("h")),
                    Call("reading", S, a, Call("snd", Id("p")), Seq(Id("h"), Apos))))), Dot));

    private static Formula SynchronizedPathFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, x, Comma, Sp, xp, Colon, Sp, X, Comma),
        Seq(Call("SynchronizedPath", S, x, xp, emptyWord), Comma),
        Seq(Forall, Sp, a, Colon, Sp, A, Comma, Sp, Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
            IffFormula(
                Call("SynchronizedPath", S, x, xp, Call("cons", a, w)),
                And(
                    Call("SynchronizedEdge", S, Pair(x, xp), a),
                    Call("SynchronizedPath", S,
                        Call("successor", S, a, x),
                        Call("successor", S, a, xp), w))), Dot),
    ]));

    private static Formula PairTraceFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, x, Comma, Sp, xp, Colon, Sp, X, Comma),
        Seq(Equal(Call("pairTrace", S, x, xp, emptyWord), Call("singleton", Pair(x, xp))), Comma),
        Seq(Forall, Sp, a, Colon, Sp, A, Comma, Sp, Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
            Equal(Call("pairTrace", S, x, xp, Call("cons", a, w)),
                Call("cons", Pair(x, xp),
                    Call("pairTrace", S,
                        Call("successor", S, a, x),
                        Call("successor", S, a, xp), w))), Dot),
    ]));

    private static Formula DeltaSumFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, x, Comma, Sp, xp, Colon, Sp, X, Comma),
        Seq(Equal(Call("deltaSum", S, x, xp, emptyWord), D(0)), Comma),
        Seq(Forall, Sp, a, Colon, Sp, A, Comma, Sp, Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
            Equal(Call("deltaSum", S, x, xp, Call("cons", a, w)),
                Seq(Paren(Seq(Call("cost", S, a, x), Sp, Minus, Sp, Call("cost", S, a, xp))),
                    Sp, Plus, Sp,
                    Call("deltaSum", S,
                        Call("successor", S, a, x),
                        Call("successor", S, a, xp), w))), Dot),
    ]));

    private static Formula SynchronouslyReachableFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, Id("X0"), Colon, Sp, SetOf(X), Comma, Sp,
            Forall, Sp, Id("p"), Colon, Sp, Product(X, X), Comma),
        Seq(IffFormula(
            Call("SynchronouslyReachable", S, Id("X0"), Id("p")),
            Seq(Exists, Sp, x, Comma, Sp, xp, Colon, Sp, X, Comma, Sp,
                Exists, Sp, w, Colon, Sp, wordType, Comma, Sp,
                And(
                    And(
                        And(Seq(x, Sp, InMacro, Sp, Id("X0")),
                            Seq(xp, Sp, InMacro, Sp, Id("X0"))),
                        Call("SynchronizedPath", S, x, xp, w)),
                    Equal(Pair(Call("stateAfter", S, x, w), Call("stateAfter", S, xp, w)), Id("p"))))), Dot),
    ]));

    private static Formula ArchiveRecoverableFormula() => Disp(new Formula.Aligned([
        Seq(CommonParameters(), Forall, Sp, Id("X0"), Colon, Sp, SetOf(X), Comma),
        Seq(IffFormula(
            Call("ArchiveRecoverable", S, Id("X0")),
            Seq(Exists, Sp, Id("Gamma"), Colon, Sp, Arrow(archiveType, Integers), Comma, Sp,
                Forall, Sp, x, Colon, Sp, X, Comma, Sp,
                Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
                Implies(
                    And(Seq(x, Sp, InMacro, Sp, Id("X0")), Call("Legal", S, x, w)),
                    Equal(Call("Gamma", Call("visibleArchive", S, x, w)), Call("clock", S, x, w))))), Dot),
    ]));

    private static Formula Recovery() => Call("ArchiveRecoverable", S, Id("X0"));

    private static Formula PathZero() => Seq(
        Forall, Sp, x, Comma, Sp, xp, Colon, Sp, X, Comma, Sp,
        Forall, Sp, w, Colon, Sp, wordType, Comma, Sp,
        Implies(
            And(
                And(Seq(x, Sp, InMacro, Sp, Id("X0")), Seq(xp, Sp, InMacro, Sp, Id("X0"))),
                Call("SynchronizedPath", S, x, xp, w)),
            Equal(Call("deltaSum", S, x, xp, w), D(0))));

    private static Formula EdgeZero() => Seq(
        Forall, Sp, Id("p"), Colon, Sp, Product(X, X), Comma, Sp,
        Forall, Sp, a, Colon, Sp, A, Comma, Sp,
        Implies(
            And(
                Call("SynchronouslyReachable", S, Id("X0"), Id("p")),
                Call("SynchronizedEdge", S, Id("p"), a)),
            Equal(
                Seq(Call("cost", S, a, Call("fst", Id("p"))), Sp, Minus, Sp,
                    Call("cost", S, a, Call("snd", Id("p")))), D(0))));

    private static Formula AmbiguityWitness() => Seq(
        Exists, Sp, x, Comma, Sp, xp, Colon, Sp, X, Comma, Sp,
        Exists, Sp, w, Colon, Sp, wordType, Comma, Sp,
        And(
            And(
                And(Seq(x, Sp, InMacro, Sp, Id("X0")), Seq(xp, Sp, InMacro, Sp, Id("X0"))),
                And(Call("Legal", S, x, w), Call("Legal", S, xp, w))),
            And(
                Equal(Call("visibleArchive", S, x, w), Call("visibleArchive", S, xp, w)),
                And(
                    NotEqual(Call("clock", S, x, w), Call("clock", S, xp, w)),
                    Seq(Call("length", w), Sp, Leq, Sp, new Formula.Power(Id("n"), D(2)))))));

    private static Formula TheoremFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, X, Comma, Sp, A, Comma, Sp, Y, Colon, Sp, Types, Comma, Sp,
            Forall, Sp, Id("n"), Colon, Sp, Naturals, Comma),
        Seq(Forall, Sp, Id("X0"), Colon, Sp, SetOf(X), Comma, Sp,
            Forall, Sp, S, Colon, Sp, Call("System", X, A, Y), Comma),
        Seq(Implies(
            And(
                And(Call("Fintype", X), And(Call("Fintype", A), Call("Fintype", Y))),
                And(
                    Equal(Call("card", X), Id("n")),
                    Call("Nonempty", Id("X0")))),
            And(
                And(IffFormula(Recovery(), PathZero()), IffFormula(PathZero(), EdgeZero())),
                Implies(Seq(Neg, Sp, Recovery()), AmbiguityWitness()))), Dot),
    ]));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class CalibrationHistoryCoarsestQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Destructive experiments solve any pair of calibration histories in one step, "
            + "but their full union is unsolvable and has no coarsest feasible history encoding.",
        H("Destructive Calibration Histories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("calibration-history-cells"),
                DeclarationHandle.Create(Prefix + "Cell"),
                H("Live history classes and retained target cells"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Histories are Fin 3, with 0, 1, 2 naming calibration classes 1, 2, 3. "
                        + "A live cell stores a nonempty set of histories and includes both possible "
                        + "target bits at every history. A known cell retains one acquired bit. "
                        + "A dead cell retains both bits after a failed destructive experiment. "
                        + "Known and dead cells describe observer knowledge; the physical device "
                        + "is in the same terminal state in both cases."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibration-history-response"),
                DeclarationHandle.Create(Prefix + "response"),
                H("Each experiment has exactly one failing history"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An experiment is named by its failing history. Experiment 0 is c, "
                        + "experiment 1 is a, and experiment 2 is b. It returns no bit when "
                        + "the history equals that index, and otherwise returns the target bit. "
                        + "Thus class 1 succeeds on a and b, class 2 on b and c, and class 3 on a and c."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibration-history-control-system"),
                DeclarationHandle.Create(Prefix + "calibrationSystem"),
                H("Attained replies determine the successor knowledge cell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The control system uses the existing ControlSystem and BoundedReachStrategy "
                        + "types. A live experiment branches to exactly the cells represented by "
                        + "responses attained at its possible histories and bits. A bit response "
                        + "produces a known cell; a failed response produces the dead cell. "
                        + "Every later experiment returns failure and preserves the retained "
                        + "target candidates, represented by a self-loop at known or dead cells. "
                        + "The goal consists exactly of known cells. No reset, source copy, "
                        + "calibration archive, or other readout is available."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibration-history-task-feasibility"),
                DeclarationHandle.Create(Prefix + "TaskFeasible"),
                H("Every encoded history class must be solvable"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any history type, control system, goal, and fixed merger of nonempty "
                        + "history sets into control states, an equivalence relation is feasible "
                        + "at horizon n if every one of its classes admits a strategy at that horizon. "
                        + "In the calibration model the merger constructs the live cell. "
                        + "The quotient cardinality counts initial history labels, rather than "
                        + "all states of a running controller. The order S <= R "
                        + "means every S-equivalent pair is R-equivalent, so R is coarser."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibration-history-trap"),
                DeclarationHandle.Create(Prefix + "trap_general"),
                H("A bad successor is enough to defeat any bounded strategy"),
                StatementSource.FromAuthor(TrapFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bad set is disjoint from the goal. At every bad state, every action "
                        + "has at least one bad successor. Induction on a bounded strategy then "
                        + "excludes success: stopping contradicts disjointness, and taking an action "
                        + "lets the environment select the bad successor. This applies to all horizons, "
                        + "rather than just to a table of short protocols."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("calibration-history-coarsest-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The universal coarsest task-sufficient encoding assertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The assertion quantifies over all small history and state types, control "
                        + "systems with small action types, goals, fixed mergers, and positive finite "
                        + "horizons. Whenever some encoding is feasible, it requires a feasible "
                        + "encoding coarser than every feasible encoding. A greatest encoding "
                        + "would also be unique, because the equivalence-relation order is antisymmetric."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibration-history-coarsest-refutation"),
                DeclarationHandle.Create(Prefix + "refutation"),
                H("Task sufficiency need not have a coarsest feasible quotient"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Call("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At horizon one, the partitions {1,2}|{3} and {1,3}|{2} are both feasible. "
                        + "A common coarsening puts all three histories in one class. That class "
                        + "has a failed first-experiment branch into the dead cell and is unsolvable. "
                        + "This single history task therefore contradicts the universal assertion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("calibration-history-coarsest-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("One-step pairwise solvability and failure of a coarsest encoding"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write W(n,A) for a bounded strategy in the calibration control system "
                            + "with horizon n from the live cell of the nonempty history set A. "
                            + "Write F(n,R) for TaskFeasible in that same system, with the live-cell "
                            + "merger, and T for possibleTargets. All displayed i and j range over "
                            + "Fin 3; R and S range over its equivalence relations.")),
                    Paragraph(Text(
                        "Every singleton and every pair has an experiment that fails on none of "
                            + "its histories. All attained responses then give a known bit in one step. "
                            + "Stopping at step zero fails because both bits are still possible. "
                            + "For the full union, each first experiment fails on its own history. "
                            + "Both target bits then have the same dead successor, whose self-loop "
                            + "satisfies the bad-set condition for every future depth.")),
                    Paragraph(Text(
                        "For each positive horizon, the partition {1,2}|{3} gives two feasible "
                            + "classes. A quotient with at most one class identifies all histories "
                            + "and would solve the impossible full union. Thus the minimum is exactly "
                            + "two. A greatest feasible relation would coarsen both {1,2}|{3} and "
                            + "{1,3}|{2}, forcing the same impossible full class. "
                            + "Equal target candidate sets and equal shortest budgets therefore "
                            + "do not justify merging calibration histories."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/Control/FiniteHorizonReachability"))]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        if (arguments.Length == 0) return Seq(Operatorname, Grp(F.Id(name)));
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Par(Formula formula) => Seq(Open, formula, Close);
    private static Formula Set(params Formula[] values)
    {
        var items = new List<Formula> { OpenBrace };
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(values[i]);
        }
        items.Add(CloseBrace);
        return Seq([.. items]);
    }

    private static Formula TrapFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), u = F.Id("u");
        Formula bad = F.Id("B"), target = F.Id("G"), system = F.Id("M");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("X"), Colon, Sp, Call("Type"), Comma, Sp, system, Colon, Sp,
            Call("ControlSystem", F.Id("X")), Comma, Sp,
            target, Comma, Sp, bad, Colon, Sp, Call("Set", F.Id("X")), Comma,
            RowBreak, Grp(),
            Par(Seq(Forall, Sp, x, Sp, InMacro, Sp, bad, Comma, Sp,
                Neg, Par(Seq(x, Sp, InMacro, Sp, target)))), Sp, Land, Sp,
            Par(Seq(Forall, Sp, x, Sp, InMacro, Sp, bad, Comma, Sp,
                Forall, Sp, u, Colon, Sp, Call("Action", system, x), Comma, Sp,
                Exists, Sp, y, Sp, InMacro, Sp, Call("successor", system, u), Comma, Sp,
                y, Sp, InMacro, Sp, bad)), RowBreak, Grp(),
            Implies, Sp, Forall, Sp, F.Id("n"), Colon, Sp, Call("Nat"), Comma, Sp,
            Forall, Sp, x, Sp, InMacro, Sp, bad, Comma, Sp,
            Neg, Call("BoundedReachStrategy", system, target, F.Id("n"), x),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ResultFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), n = F.Id("n");
        Formula r = F.Id("R"), s = F.Id("S"), histories = Call("Fin", D(3));
        Formula singles = Par(Seq(Forall, Sp, i, Colon, Sp, histories, Comma, Sp,
            Call("W", D(1), Set(i)), Sp, Land, Sp, Neg, Call("W", D(0), Set(i))));
        Formula pairs = Par(Seq(Forall, Sp, i, Comma, Sp, j, Colon, Sp, histories, Comma, Sp,
            Call("W", D(1), Set(i, j)), Sp, Land, Sp, Neg, Call("W", D(0), Set(i, j))));
        Formula impossible = Par(Seq(Forall, Sp, n, Colon, Sp, Call("Nat"), Comma, Sp,
            Neg, Call("W", n, Set(D(0), D(1), D(2)))));
        Formula targets = Par(Seq(Forall, Sp, i, Colon, Sp, histories, Comma, Sp,
            Call("T", Call("live", Set(i))), Sp, Eq, Sp, Call("univ")));
        Formula size = Call("card", Call("Quotient", r));
        Formula minimum = Par(Seq(Exists, Sp, r, Comma, Sp,
            Call("F", n, r), Sp, Land, Sp, size, Sp, Eq, Sp, D(2)));
        Formula lower = Par(Seq(Forall, Sp, r, Comma, Sp,
            Call("F", n, r), Sp, Implies, Sp, D(2), Sp, Leq, Sp, size));
        Formula greatest = Seq(Exists, Sp, r, Comma, Sp,
            Call("F", n, r), Sp, Land, Sp,
            Par(Seq(Forall, Sp, s, Comma, Sp, Call("F", n, s), Sp, Implies, Sp,
                s, Sp, Leq, Sp, r)));
        Formula encodings = Par(Seq(Forall, Sp, n, Colon, Sp, Call("Nat"), Comma, Sp,
            D(1), Sp, Leq, Sp, n, Sp, Implies, Sp,
            Par(Seq(minimum, Sp, Land, Sp, lower, Sp, Land, Sp, Neg, Par(greatest)))));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            singles, Sp, Land, RowBreak, Grp(), pairs, Sp, Land, RowBreak, Grp(),
            impossible, Sp, Land, RowBreak, Grp(), targets, Sp, Land, RowBreak, Grp(),
            encodings, Sp, Land, RowBreak, Grp(), Neg, Call("claim"),
            End, Grp(F.Id("gathered"))));
    }
}

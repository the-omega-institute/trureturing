using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class TaskModalGreatestDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite task-modal tests characterize the greatest task-preserving successor equivalence.",
        H("Task-modal equivalence and successor matching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("task-modal-greatest"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/TaskModalGreatest.result"),
                H("The greatest stable task equivalence for image-finite transitions"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be any state type, U any action type, J any task-index type, "
                        + "and Y a family of output types indexed by J. Each task f(j) maps X "
                        + "to Y(j). A labelled relation R(u,x,x') describes actual successors. "
                        + "The sole finiteness assumption is that, for every u and x, the set "
                        + "of x' with R(u,x,x') is finite.")),
                    Paragraph(Text(
                        "TaskFormula is generated independently by truth, every atom "
                        + "f(j)=v, negation, binary conjunction, and existential labelled "
                        + "modalities. Finite conjunctions are iterated binary conjunctions "
                        + "ending in truth. The predicate task_satisfies interprets an atom "
                        + "by equality of the current task value, and a modality by one "
                        + "actual successor satisfying its entire argument. TaskModalEq(R,f) "
                        + "is agreement on every such finite formula.")),
                    Paragraph(Text(
                        "Tasks(E,f) means that E-related states have equal values for every "
                        + "task. Match(E,R) means that each actual successor of either state "
                        + "has an E-related actual successor of the other, with the same "
                        + "action label. Both conditions are expanded below. TaskModalEq is "
                        + "an equivalence satisfying these conditions and containing every "
                        + "other equivalence satisfying them.")),
                    Paragraph(Math(Disp(ConditionsFormula()))),
                    Paragraph(Text(
                        "Encode an observation (j,v) as a self-loop present exactly when "
                        + "f(j,x)=v, using the disjoint sum of action labels and dependent "
                        + "task-value pairs. Translate each task atom to its observation "
                        + "diamond of truth. Conversely, translate an observation diamond "
                        + "of a formula to the corresponding task atom conjoined with the "
                        + "translated formula at the same state. Structural induction proves "
                        + "that both translations preserve satisfaction for every formula "
                        + "and every state, without a finiteness assumption.")),
                    Paragraph(Text(
                        "For Hennessy-Milner formulas, a failed successor match supplies a "
                        + "distinguishing formula for each potential matching successor. "
                        + "Negation orients these formulas, and image-finiteness permits "
                        + "their conjunction. Its diamond contradicts agreement of the "
                        + "source states. An empty set of potential matches gives the empty "
                        + "conjunction, truth. The reverse inclusion follows by induction "
                        + "on Hennessy-Milner formulas and the satisfaction translations.")),
                    Paragraph(Text(
                        "The state, action, and task families may be infinite. Transitions "
                        + "may branch or be absent. Conjunction inside a modality is tested "
                        + "at one common successor, so agreement of separate possible "
                        + "traces does not replace branching agreement. No conclusion for "
                        + "arbitrary infinitely branching systems is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ResultFormula()
    {
        Formula r = F.Id("R"), f = F.Id("f"), e = F.Id("E");
        Formula emod = Call("TaskModalEq", r, f);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("X"), Comma, F.Id("U"), Comma, F.Id("J"), Comma,
            F.Id("Y"), Comma, r, Comma, f, Comma, Sp,
            Call("ImageFinite", r), Sp, Rightarrow, RowBreak, Grp(),
            Call("Equivalence", emod), Sp, Land, Sp,
            Call("Tasks", emod, f), Sp, Land, Sp,
            Call("Match", emod, r), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, e, Comma, Sp,
            Call("Equivalence", e), Sp, Land, Sp, Call("Tasks", e, f), Sp, Land, Sp,
            Call("Match", e, r), Sp, Rightarrow, Sp,
            Forall, Sp, F.Id("x"), Comma, F.Id("y"), Comma, Sp,
            Call("E", F.Id("x"), F.Id("y")), Sp, Rightarrow, Sp,
            Call("TaskModalEq", r, f, F.Id("x"), F.Id("y")), Close,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ConditionsFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), xp = F.Id("s"), yp = F.Id("t");
        Formula u = F.Id("u"), j = F.Id("j"), e = F.Id("E"), r = F.Id("R"), f = F.Id("f");
        Formula forward = Seq(Forall, Sp, xp, Comma, Sp, Call("R", u, x, xp), Sp,
            Rightarrow, Sp, Exists, Sp, yp, Comma, Sp,
            Call("R", u, y, yp), Sp, Land, Sp, Call("E", xp, yp));
        Formula reverse = Seq(Forall, Sp, yp, Comma, Sp, Call("R", u, y, yp), Sp,
            Rightarrow, Sp, Exists, Sp, xp, Comma, Sp,
            Call("R", u, x, xp), Sp, Land, Sp, Call("E", xp, yp));
        return Seq(Begin, Grp(F.Id("gathered")),
            Call("Tasks", e, f), Sp, Iff, Sp,
            Forall, Sp, x, Comma, y, Comma, Sp, Call("E", x, y), Sp, Rightarrow, Sp,
            Forall, Sp, j, Comma, Sp, Call("f", j, x), Sp, Eq, Sp, Call("f", j, y),
            RowBreak, Grp(),
            Call("Match", e, r), Sp, Iff, Sp,
            Forall, Sp, x, Comma, y, Comma, Sp, Call("E", x, y), Sp, Rightarrow, Sp,
            Forall, Sp, u, Comma, RowBreak, Grp(),
            Open, forward, Close, Sp, Land, Sp, Open, reverse, Close,
            End, Grp(F.Id("gathered")));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class FiniteHorizonKernelRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-horizon behavior kernels descend by one new coordinate, intersect to the complete kernel, and stabilize at the finite completion depth.",
        H("Finite Horizon Kernel Recurrence"),
        Blocks(
            Theorem(
                "finite-horizon-kernel-succ-iff",
                "finite_horizon_kernel_succ_iff",
                FiniteHorizonKernelSuccIffFormula(),
                "Finite Horizon Kernel Succ iff",
                "Adding one horizon coordinate intersects the previous kernel with equality of the new terminal observation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "finite-horizon-kernel-antitone",
                "finite_horizon_kernel_antitone",
                FiniteHorizonKernelAntitoneFormula(),
                "Finite Horizon Kernel Antitone",
                "Longer observation horizons yield finer kernels.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "complete-kernel-eq-i-inf-finite-horizon",
                "complete_kernel_eq_iInf_finite_horizon",
                CompleteKernelEqIinfFiniteHorizonFormula(),
                "Complete Kernel eq I Inf Finite Horizon",
                "The complete behavior kernel is the infimum of all finite-horizon kernels.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "finite-horizon-first-new-coordinate-strict",
                "finite_horizon_first_new_coordinate_strict",
                FiniteHorizonFirstNewCoordinateStrictFormula(),
                "Finite Horizon First New Coordinate Strict",
                "A first separating terminal coordinate certifies strict refinement at the next finite horizon.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "finite-horizon-stabilizes-at-completion-depth",
                "finite_horizon_stabilizes_at_completionDepth",
                FiniteHorizonStabilizesAtCompletiondepthFormula(),
                "Finite Horizon Stabilizes At Completion Depth",
                "On a finite state space, the canonical completion depth already has the complete infinite-horizon kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula FiniteHorizonKernelSuccIffFormula() => Statement(
    [Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("O")), Seq(F.Id("Type"))), Typed(Seq(F.Id("tau")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("O")))), Typed(Seq(F.Id("m")), Seq(Mathbb, Grp(F.Id("N")))), Typed(Seq(F.Id("y")), Seq(F.Id("Y"))), Typed(Seq(F.Id("y"), Apos), Seq(F.Id("Y")))],
        [],
        [],
        Seq(F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, Open, F.Id("m"), Sp, Plus, Sp, D(1), Close, Sp, F.Id("y"), Sp, F.Id("y"), Apos, Sp, Leftrightarrow, Sp, F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, F.Id("m"), Sp, F.Id("y"), Sp, F.Id("y"), Apos, Sp, Land, Sp, F.Id("q"), Sp, Open, Open, F.Id("tau"), Caret, Grp(OpenBracket, F.Id("m"), Sp, Plus, Sp, D(1), CloseBracket), Close, Sp, F.Id("y"), Close, Sp, Eq, Sp, F.Id("q"), Sp, Open, Open, F.Id("tau"), Caret, Grp(OpenBracket, F.Id("m"), Sp, Plus, Sp, D(1), CloseBracket), Close, Sp, F.Id("y"), Apos, Close));

private static Formula FiniteHorizonKernelAntitoneFormula() => Statement(
    [Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("O")), Seq(F.Id("Type"))), Typed(Seq(F.Id("tau")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("O")))), Typed(Seq(F.Id("m")), Seq(Mathbb, Grp(F.Id("N")))), Typed(Seq(F.Id("n")), Seq(Mathbb, Grp(F.Id("N"))))],
        [],
        [Seq(F.Id("m"), Sp, Leq, Sp, F.Id("n"))],
        Seq(F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, F.Id("n"), Sp, Leq, Sp, F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, F.Id("m")));

private static Formula CompleteKernelEqIinfFiniteHorizonFormula() => Statement(
    [Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("O")), Seq(F.Id("Type"))), Typed(Seq(F.Id("tau")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("O"))))],
        [],
        [],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("completeItinerary"), Sp, F.Id("tau"), Sp, F.Id("q"), Close, Sp, Eq, Sp, F.Id("iInf"), Sp, F.Id("m"), Comma, Sp, F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, F.Id("m")));

private static Formula FiniteHorizonFirstNewCoordinateStrictFormula() => Statement(
    [Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("O")), Seq(F.Id("Type"))), Typed(Seq(F.Id("tau")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("O")))), Typed(Seq(F.Id("m")), Seq(Mathbb, Grp(F.Id("N")))), Typed(Seq(F.Id("y")), Seq(F.Id("Y"))), Typed(Seq(F.Id("y"), Apos), Seq(F.Id("Y")))],
        [],
        [Seq(F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, F.Id("m"), Sp, F.Id("y"), Sp, F.Id("y"), Apos), Seq(F.Id("q"), Sp, Open, Open, F.Id("tau"), Caret, Grp(OpenBracket, F.Id("m"), Sp, Plus, Sp, D(1), CloseBracket), Close, Sp, F.Id("y"), Close, Sp, Neq, Sp, F.Id("q"), Sp, Open, Open, F.Id("tau"), Caret, Grp(OpenBracket, F.Id("m"), Sp, Plus, Sp, D(1), CloseBracket), Close, Sp, F.Id("y"), Apos, Close)],
        Seq(F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, Open, F.Id("m"), Sp, Plus, Sp, D(1), Close, Sp, Lt, Sp, F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, F.Id("m")));

private static Formula FiniteHorizonStabilizesAtCompletiondepthFormula() => Statement(
    [Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("O")), Seq(F.Id("Type"))), Typed(Seq(F.Id("tau")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("O"))))],
        [Seq(OpenBracket, Call("Fintype", Seq(F.Id("Y"))), CloseBracket)],
        [],
        Seq(F.Id("finiteHorizonKernel"), Sp, F.Id("tau"), Sp, F.Id("q"), Sp, Open, F.Id("completionDepth"), Sp, F.Id("tau"), Sp, F.Id("q"), Close, Sp, Eq, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("completeItinerary"), Sp, F.Id("tau"), Sp, F.Id("q"), Close));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class WormholeKernelTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Bridges/WormholeKernelTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wormhole composition records exact observer-kernel loss.",
        H("Wormhole Kernel Transport"),
        Blocks(
            Theorem(
                "kernel-forward-invariant",
                "kernel_forward_invariant",
                KernelForwardInvariantFormula(),
                "Kernel Forward Invariant",
                "The observation kernel of a wormhole is forward-invariant under the source dynamics.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "kernel-le-composite",
                "kernel_le_composite",
                KernelLeCompositeFormula(),
                "Kernel le Composite",
                "Postcomposing a wormhole can only enlarge its source observer kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "kernel-eq-composite-of-outer-injective",
                "kernel_eq_composite_of_outer_injective",
                KernelEqCompositeOfOuterInjectiveFormula(),
                "Kernel eq Composite Of Outer Injective",
                "An injective outer wormhole preserves the source observer kernel exactly.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strict-kernel-growth-of-outer-collision",
                "strict_kernel_growth_of_outer_collision",
                StrictKernelGrowthOfOuterCollisionFormula(),
                "Strict Kernel Growth Of Outer Collision",
                "A pair visible after the first bridge but collapsed by the second bridge witnesses strict growth of the composite kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strict-growth-refutes-outer-injectivity",
                "strict_growth_refutes_outer_injectivity",
                StrictGrowthRefutesOuterInjectivityFormula(),
                "Strict Growth Refutes Outer Injectivity",
                "Strict information loss through a composite refutes injectivity of the outer bridge.",
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

private static Formula KernelForwardInvariantFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("bridge")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("first")), Seq(F.Id("source"), Dot, F.Id("State"))), Typed(Seq(F.Id("second")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("bridge"), Dot, F.Id("map"), Sp, F.Id("first"), Sp, F.Id("second"))],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("bridge"), Dot, F.Id("map"), Sp, Open, F.Id("source"), Dot, F.Id("step"), Sp, F.Id("first"), Close, Sp, Open, F.Id("source"), Dot, F.Id("step"), Sp, F.Id("second"), Close));

private static Formula KernelLeCompositeFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("middle")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("first")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("middle"))), Typed(Seq(F.Id("second")), Seq(F.Id("Wormhole"), Sp, F.Id("middle"), Sp, F.Id("target")))],
        [],
        [],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("first"), Dot, F.Id("map"), Sp, Leq, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("compose"), Sp, F.Id("second"), Sp, F.Id("first"), Close, Dot, F.Id("map")));

private static Formula KernelEqCompositeOfOuterInjectiveFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("middle")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("first")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("middle"))), Typed(Seq(F.Id("second")), Seq(F.Id("Wormhole"), Sp, F.Id("middle"), Sp, F.Id("target")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("second"), Dot, F.Id("map"))],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("compose"), Sp, F.Id("second"), Sp, F.Id("first"), Close, Dot, F.Id("map"), Sp, Eq, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("first"), Dot, F.Id("map")));

private static Formula StrictKernelGrowthOfOuterCollisionFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("middle")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("first")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("middle"))), Typed(Seq(F.Id("second")), Seq(F.Id("Wormhole"), Sp, F.Id("middle"), Sp, F.Id("target"))), Typed(Seq(F.Id("left")), Seq(F.Id("source"), Dot, F.Id("State"))), Typed(Seq(F.Id("right")), Seq(F.Id("source"), Dot, F.Id("State")))],
        [],
        [Seq(F.Id("first"), Dot, F.Id("map"), Sp, F.Id("left"), Sp, Neq, Sp, F.Id("first"), Dot, F.Id("map"), Sp, F.Id("right")), Seq(F.Id("second"), Dot, F.Id("map"), Sp, Open, F.Id("first"), Dot, F.Id("map"), Sp, F.Id("left"), Close, Sp, Eq, Sp, F.Id("second"), Dot, F.Id("map"), Sp, Open, F.Id("first"), Dot, F.Id("map"), Sp, F.Id("right"), Close)],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("first"), Dot, F.Id("map"), Sp, Lt, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("compose"), Sp, F.Id("second"), Sp, F.Id("first"), Close, Dot, F.Id("map")));

private static Formula StrictGrowthRefutesOuterInjectivityFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("middle")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("target")), Seq(F.Id("DynamicalWorld"))), Typed(Seq(F.Id("first")), Seq(F.Id("Wormhole"), Sp, F.Id("source"), Sp, F.Id("middle"))), Typed(Seq(F.Id("second")), Seq(F.Id("Wormhole"), Sp, F.Id("middle"), Sp, F.Id("target")))],
        [],
        [Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("first"), Dot, F.Id("map"), Sp, Lt, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("compose"), Sp, F.Id("second"), Sp, F.Id("first"), Close, Dot, F.Id("map"))],
        Seq(Neg, Sp, F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("second"), Dot, F.Id("map")));

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

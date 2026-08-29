using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCompletionFlow;

internal sealed class SimpleZeroCompletionVelocityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nondegenerate zero-thread chain equation determines its completion velocity by the ratio of completion and state derivatives.",
        H("Simple Zero Completion Velocity"),
        Blocks(
            Theorem(
                "zero-completion-velocity-eq-of-chain",
                "zero_completion_velocity_eq_of_chain",
                ZeroCompletionVelocityEqOfChainFormula(),
                "Zero Completion Velocity eq Of Chain",
                "Algebraic extraction of the simple-zero completion velocity from the chain rule identity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-satisfies-chain",
                "zero_completion_velocity_satisfies_chain",
                ZeroCompletionVelocitySatisfiesChainFormula(),
                "Zero Completion Velocity Satisfies Chain",
                "Substitution back into the chain equation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-scale-invariant",
                "zero_completion_velocity_scale_invariant",
                ZeroCompletionVelocityScaleInvariantFormula(),
                "Zero Completion Velocity Scale Invariant",
                "Common nonzero rescaling of the analytic family leaves zero velocity unchanged.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-eq-zero-iff",
                "zero_completion_velocity_eq_zero_iff",
                ZeroCompletionVelocityEqZeroIffFormula(),
                "Zero Completion Velocity eq Zero iff",
                "At a simple zero, vanishing completion velocity is equivalent to vanishing completion-direction forcing.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-ne-zero",
                "zero_completion_velocity_ne_zero",
                ZeroCompletionVelocityNeZeroFormula(),
                "Zero Completion Velocity ne Zero",
                "A nonzero forcing term yields a nonzero velocity at a simple zero.",
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

private static Formula ZeroCompletionVelocityEqOfChainFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("completionDerivative")), Seq(F.Id("K"))), Typed(Seq(F.Id("stateDerivative")), Seq(F.Id("K"))), Typed(Seq(F.Id("velocity")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("stateDerivative"), Sp, Neq, Sp, D(0)), Seq(F.Id("completionDerivative"), Sp, Plus, Sp, F.Id("stateDerivative"), Sp, Times, Sp, F.Id("velocity"), Sp, Eq, Sp, D(0))],
        Seq(F.Id("velocity"), Sp, Eq, Sp, F.Id("zeroCompletionVelocity"), Sp, F.Id("completionDerivative"), Sp, F.Id("stateDerivative")));

private static Formula ZeroCompletionVelocitySatisfiesChainFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("completionDerivative")), Seq(F.Id("K"))), Typed(Seq(F.Id("stateDerivative")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("stateDerivative"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("completionDerivative"), Sp, Plus, Sp, F.Id("stateDerivative"), Sp, Times, Sp, F.Id("zeroCompletionVelocity"), Sp, F.Id("completionDerivative"), Sp, F.Id("stateDerivative"), Sp, Eq, Sp, D(0)));

private static Formula ZeroCompletionVelocityScaleInvariantFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("c")), Seq(F.Id("K"))), Typed(Seq(F.Id("completionDerivative")), Seq(F.Id("K"))), Typed(Seq(F.Id("stateDerivative")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("c"), Sp, Neq, Sp, D(0)), Seq(F.Id("stateDerivative"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("zeroCompletionVelocity"), Sp, Open, F.Id("c"), Sp, Times, Sp, F.Id("completionDerivative"), Close, Sp, Open, F.Id("c"), Sp, Times, Sp, F.Id("stateDerivative"), Close, Sp, Eq, Sp, F.Id("zeroCompletionVelocity"), Sp, F.Id("completionDerivative"), Sp, F.Id("stateDerivative")));

private static Formula ZeroCompletionVelocityEqZeroIffFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("completionDerivative")), Seq(F.Id("K"))), Typed(Seq(F.Id("stateDerivative")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("stateDerivative"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("zeroCompletionVelocity"), Sp, F.Id("completionDerivative"), Sp, F.Id("stateDerivative"), Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp, F.Id("completionDerivative"), Sp, Eq, Sp, D(0)));

private static Formula ZeroCompletionVelocityNeZeroFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("completionDerivative")), Seq(F.Id("K"))), Typed(Seq(F.Id("stateDerivative")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("completionDerivative"), Sp, Neq, Sp, D(0)), Seq(F.Id("stateDerivative"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("zeroCompletionVelocity"), Sp, F.Id("completionDerivative"), Sp, F.Id("stateDerivative"), Sp, Neq, Sp, D(0)));

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

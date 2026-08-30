using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCompletionFlow;

internal sealed class NewtonCompletionFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Newton completion vector is scale invariant, detects roots under a regular derivative, and exactly completes affine zero models in one step.",
        H("Newton Completion Field"),
        Blocks(
            Theorem(
                "newton-completion-vector-eq-zero-iff",
                "newton_completion_vector_eq_zero_iff",
                NewtonCompletionVectorEqZeroIffFormula(),
                "Newton Completion Vector eq Zero iff",
                "At a regular point, the Newton vector vanishes exactly at a root.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "newton-completion-vector-scale-invariant",
                "newton_completion_vector_scale_invariant",
                NewtonCompletionVectorScaleInvariantFormula(),
                "Newton Completion Vector Scale Invariant",
                "Common nonzero rescaling of a function and its derivative field leaves the Newton vector unchanged.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-newton-completion-vector",
                "affine_newton_completion_vector",
                AffineNewtonCompletionVectorFormula(),
                "Affine Newton Completion Vector",
                "The Newton vector of an affine simple-zero model points exactly from the current point to its root.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-newton-completion-step",
                "affine_newton_completion_step",
                AffineNewtonCompletionStepFormula(),
                "Affine Newton Completion Step",
                "Consequently, an affine simple-zero model completes in one Newton step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "root-fixed-by-newton-completion",
                "root_fixed_by_newton_completion",
                RootFixedByNewtonCompletionFormula(),
                "Root Fixed By Newton Completion",
                "A genuine regular root is fixed by the Newton completion step.",
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

private static Formula NewtonCompletionVectorEqZeroIffFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("F")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("dF")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("s")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("dF"), Sp, F.Id("s"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("newtonCompletionVector"), Sp, F.Id("F"), Sp, F.Id("dF"), Sp, F.Id("s"), Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp, F.Id("F"), Sp, F.Id("s"), Sp, Eq, Sp, D(0)));

private static Formula NewtonCompletionVectorScaleInvariantFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("c")), Seq(F.Id("K"))), Typed(Seq(F.Id("F")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("dF")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("s")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("c"), Sp, Neq, Sp, D(0)), Seq(F.Id("dF"), Sp, F.Id("s"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("newtonCompletionVector"), Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("c"), Sp, Times, Sp, F.Id("F"), Sp, F.Id("z"), Close, Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("c"), Sp, Times, Sp, F.Id("dF"), Sp, F.Id("z"), Close, Sp, F.Id("s"), Sp, Eq, Sp, F.Id("newtonCompletionVector"), Sp, F.Id("F"), Sp, F.Id("dF"), Sp, F.Id("s")));

private static Formula AffineNewtonCompletionVectorFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("a")), Seq(F.Id("K"))), Typed(Seq(F.Id("root")), Seq(F.Id("K"))), Typed(Seq(F.Id("s")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("a"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("newtonCompletionVector"), Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("a"), Sp, Times, Sp, Open, F.Id("z"), Sp, Minus, Sp, F.Id("root"), Close, Close, Sp, Open, LambdaLower, Sp, F.Id("value"), Sp, Mapsto, Sp, F.Id("a"), Close, Sp, F.Id("s"), Sp, Eq, Sp, F.Id("root"), Sp, Minus, Sp, F.Id("s")));

private static Formula AffineNewtonCompletionStepFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("a")), Seq(F.Id("K"))), Typed(Seq(F.Id("root")), Seq(F.Id("K"))), Typed(Seq(F.Id("s")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("a"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("newtonCompletionStep"), Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("a"), Sp, Times, Sp, Open, F.Id("z"), Sp, Minus, Sp, F.Id("root"), Close, Close, Sp, Open, LambdaLower, Sp, F.Id("value"), Sp, Mapsto, Sp, F.Id("a"), Close, Sp, F.Id("s"), Sp, Eq, Sp, F.Id("root")));

private static Formula RootFixedByNewtonCompletionFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("F")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("dF")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("root")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("F"), Sp, F.Id("root"), Sp, Eq, Sp, D(0))],
        Seq(F.Id("newtonCompletionStep"), Sp, F.Id("F"), Sp, F.Id("dF"), Sp, F.Id("root"), Sp, Eq, Sp, F.Id("root")));

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

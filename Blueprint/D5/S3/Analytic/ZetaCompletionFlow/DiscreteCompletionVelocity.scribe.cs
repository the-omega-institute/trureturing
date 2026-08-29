using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCompletionFlow;

internal sealed class DiscreteCompletionVelocityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCompletionFlow/DiscreteCompletionVelocity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-difference completion velocity is a Newton predictor and exactly recovers root displacement for affine layer changes.",
        H("Discrete Completion Velocity"),
        Blocks(
            Theorem(
                "completion-layer-difference-at-root",
                "completion_layer_difference_at_root",
                CompletionLayerDifferenceAtRootFormula(),
                "Completion Layer Difference At Root",
                "At a current root, the layer difference is simply the next layer's residual at that point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "predicted-discrete-velocity-at-root",
                "predicted_discrete_velocity_at_root",
                PredictedDiscreteVelocityAtRootFormula(),
                "Predicted Discrete Velocity At Root",
                "Root-specialized form of the discrete predictor.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "predicted-discrete-velocity-eq-zero-iff",
                "predicted_discrete_velocity_eq_zero_iff",
                PredictedDiscreteVelocityEqZeroIffFormula(),
                "Predicted Discrete Velocity eq Zero iff",
                "At a regular current root, a zero predictor is equivalent to the next layer also vanishing at the same point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-layer-predicted-velocity",
                "affine_layer_predicted_velocity",
                AffineLayerPredictedVelocityFormula(),
                "Affine Layer Predicted Velocity",
                "Exact affine layer model: shifting the root by delta produces predicted velocity delta.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-layer-prediction-realized",
                "affine_layer_prediction_realized",
                AffineLayerPredictionRealizedFormula(),
                "Affine Layer Prediction Realized",
                "The affine prediction agrees with the actual next-layer root.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "predicted-discrete-velocity-scale-invariant",
                "predicted_discrete_velocity_scale_invariant",
                PredictedDiscreteVelocityScaleInvariantFormula(),
                "Predicted Discrete Velocity Scale Invariant",
                "Common nonzero rescaling of both layers and the derivative field leaves the prediction unchanged.",
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

private static Formula CompletionLayerDifferenceAtRootFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("F")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("Fnext")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("root")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("F"), Sp, F.Id("root"), Sp, Eq, Sp, D(0))],
        Seq(F.Id("completionLayerDifference"), Sp, F.Id("Fnext"), Sp, F.Id("F"), Sp, F.Id("root"), Sp, Eq, Sp, F.Id("Fnext"), Sp, F.Id("root")));

private static Formula PredictedDiscreteVelocityAtRootFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("F")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("Fnext")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("dF")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("root")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("F"), Sp, F.Id("root"), Sp, Eq, Sp, D(0))],
        Seq(F.Id("predictedDiscreteVelocity"), Sp, F.Id("F"), Sp, F.Id("Fnext"), Sp, F.Id("dF"), Sp, F.Id("root"), Sp, Eq, Sp, Minus, F.Id("Fnext"), Sp, F.Id("root"), Sp, Slash, Sp, F.Id("dF"), Sp, F.Id("root")));

private static Formula PredictedDiscreteVelocityEqZeroIffFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("F")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("Fnext")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("dF")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("root")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("F"), Sp, F.Id("root"), Sp, Eq, Sp, D(0)), Seq(F.Id("dF"), Sp, F.Id("root"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("predictedDiscreteVelocity"), Sp, F.Id("F"), Sp, F.Id("Fnext"), Sp, F.Id("dF"), Sp, F.Id("root"), Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp, F.Id("Fnext"), Sp, F.Id("root"), Sp, Eq, Sp, D(0)));

private static Formula AffineLayerPredictedVelocityFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("a")), Seq(F.Id("K"))), Typed(Seq(F.Id("root")), Seq(F.Id("K"))), Typed(Seq(F.Id("delta")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("a"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("predictedDiscreteVelocity"), Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("a"), Sp, Times, Sp, Open, F.Id("z"), Sp, Minus, Sp, F.Id("root"), Close, Close, Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("a"), Sp, Times, Sp, Open, F.Id("z"), Sp, Minus, Sp, Open, F.Id("root"), Sp, Plus, Sp, F.Id("delta"), Close, Close, Close, Sp, Open, LambdaLower, Sp, F.Id("value"), Sp, Mapsto, Sp, F.Id("a"), Close, Sp, F.Id("root"), Sp, Eq, Sp, F.Id("delta")));

private static Formula AffineLayerPredictionRealizedFormula()
{
    Formula k = F.Id("K");
    Formula a = F.Id("a");
    Formula root = F.Id("root");
    Formula delta = F.Id("delta");
    Formula z = F.Id("z");
    Formula fNext = F.Id("Fnext");
    Formula affineCurrent = Seq(
        LambdaLower, Sp, z, Colon, Sp, k, Sp, Mapsto, Sp,
        Multiply(a, Subtract(z, root)));
    Formula affineNext = Seq(
        LambdaLower, Sp, z, Colon, Sp, k, Sp, Mapsto, Sp,
        Multiply(a, Subtract(z, Add(root, delta))));
    Formula constantDerivative = Seq(
        LambdaLower, Sp, z, Colon, Sp, k, Sp, Mapsto, Sp, a);
    Formula velocity = Call(
        "predictedDiscreteVelocity",
        affineCurrent,
        fNext,
        constantDerivative,
        root);
    Formula conclusion = Seq(
        Operatorname, Grp(F.Id("let")), Sp, fNext, Colon, Sp,
        new Formula.TypeArrow(k, k), Sp, Eq, Sp, affineNext,
        Comma, RowBreak, Grp(),
        Operatorname, Grp(F.Id("let")), Sp, F.Id("velocity"), Sp, Eq, Sp,
        velocity, Comma, RowBreak, Grp(),
        Call("Fnext", Add(root, F.Id("velocity"))), Sp, Eq, Sp, D(0));

    return Statement(
        [Typed(k, F.Id("Type")), Typed(a, k), Typed(root, k), Typed(delta, k)],
        [Seq(OpenBracket, Call("Field", k), CloseBracket)],
        [Seq(a, Sp, Neq, Sp, D(0))],
        conclusion);
}

private static Formula PredictedDiscreteVelocityScaleInvariantFormula() => Statement(
    [Typed(Seq(F.Id("K")), Seq(F.Id("Type"))), Typed(Seq(F.Id("c")), Seq(F.Id("K"))), Typed(Seq(F.Id("F")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("Fnext")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("dF")), new Formula.TypeArrow(Seq(F.Id("K")), Seq(F.Id("K")))), Typed(Seq(F.Id("s")), Seq(F.Id("K")))],
        [Seq(OpenBracket, Call("Field", Seq(F.Id("K"))), CloseBracket)],
        [Seq(F.Id("c"), Sp, Neq, Sp, D(0)), Seq(F.Id("dF"), Sp, F.Id("s"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("predictedDiscreteVelocity"), Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("c"), Sp, Times, Sp, F.Id("F"), Sp, F.Id("z"), Close, Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("c"), Sp, Times, Sp, F.Id("Fnext"), Sp, F.Id("z"), Close, Sp, Open, LambdaLower, Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("c"), Sp, Times, Sp, F.Id("dF"), Sp, F.Id("z"), Close, Sp, F.Id("s"), Sp, Eq, Sp, F.Id("predictedDiscreteVelocity"), Sp, F.Id("F"), Sp, F.Id("Fnext"), Sp, F.Id("dF"), Sp, F.Id("s")));

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

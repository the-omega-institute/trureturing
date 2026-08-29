using static StrataLint.Scribe.DefinitionDsl;

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
                "Completion Layer Difference At Root",
                "At a current root, the layer difference is simply the next layer's residual at that point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "predicted-discrete-velocity-at-root",
                "predicted_discrete_velocity_at_root",
                "Predicted Discrete Velocity At Root",
                "Root-specialized form of the discrete predictor.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "predicted-discrete-velocity-eq-zero-iff",
                "predicted_discrete_velocity_eq_zero_iff",
                "Predicted Discrete Velocity eq Zero iff",
                "At a regular current root, a zero predictor is equivalent to the next layer also vanishing at the same point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-layer-predicted-velocity",
                "affine_layer_predicted_velocity",
                "Affine Layer Predicted Velocity",
                "Exact affine layer model: shifting the root by delta produces predicted velocity delta.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-layer-prediction-realized",
                "affine_layer_prediction_realized",
                "Affine Layer Prediction Realized",
                "The affine prediction agrees with the actual next-layer root.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "predicted-discrete-velocity-scale-invariant",
                "predicted_discrete_velocity_scale_invariant",
                "Predicted Discrete Velocity Scale Invariant",
                "Common nonzero rescaling of both layers and the derivative field leaves the prediction unchanged.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}

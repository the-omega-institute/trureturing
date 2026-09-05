using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class HoKalmanPredictionBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite noisy Ho-Kalman reconstruction with explicit arithmetic certificates.",
        H("HoKalmanPredictionBudget"),
        Blocks(
            Describe.Lean(DescribeId.Create("state-budget"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.stateBudget"), H("stateBudget"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("An arithmetic recurrence propagates initial input-map error and transition error. It is executable over rational numbers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("markov-budget"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markovBudget"), H("markovBudget"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The state-error recurrence and the computed output-map budget yield a finite-horizon Markov-parameter error certificate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("output-error-budget"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.outputErrorBudget"), H("outputErrorBudget"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every numeric input to this rational budget comes from finite observed samples, the supplied uncertainty, and the actual returned model."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cast-state-budget"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_stateBudget"), H("cast stateBudget"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Induction proves that rational budget evaluation agrees with its real semantic interpretation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cast-markov-budget"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_markovBudget"), H("cast markovBudget"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The computed rational output budget agrees with the corresponding real arithmetic expression."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-matrix-pow"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.realMatrix_pow"), H("realMatrix pow"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Real interpretation preserves every matrix power, closing the bridge from rational predicted outputs to real behavior."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("markov-error-le"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markov_error_le"), H("markov error le"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Induction through the actual two state systems proves the error recurrence and output inequality. Stability and diagonalizability are unnecessary for these finite-horizon bounds."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("run-prediction-error-bound"), DeclarationHandle.Create("D5/S3/Observer/Hankel/HoKalmanPredictionBudget.run_prediction_error_bound"), H("run prediction error bound"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The terminal theorem bounds every Markov prediction of the actual rational program against every compatible real order-r system by a fully rational certificate. The bound may grow with the horizon; no uniform stability guarantee is asserted."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/NoisyHoKalmanRecovery"))]));
}

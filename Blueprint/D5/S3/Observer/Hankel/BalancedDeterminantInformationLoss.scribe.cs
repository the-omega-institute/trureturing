using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class BalancedDeterminantInformationLossDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrarily small certified input-output error can delete a fixed state-determinant zero, even with bijective ports.",
        H("Balanced Determinant Information Loss"),
        Blocks(
            Describe.Lean(DescribeId.Create("dynamics"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.dynamics"), H("Fixed state dynamics"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal state matrix has entries one half and one quarter, independent of the port amplitude."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("port"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.port"), H("Nonzero input and output ports"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both input and output are the same diagonal matrix with entries one and epsilon."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weights"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.weights"), H("Exact diagonal Stein weights"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common weights are four thirds and sixteen epsilon squared divided by fifteen."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("port-injective"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.port_injective"), H("Instantaneous state distinction"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive epsilon, the actual output port is injective. The discarded state is not an invisible zero-coupled channel."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("port-surjective"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.port_surjective"), H("One-input reachability"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An explicit division in the second coordinate proves surjectivity of the actual input port."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stein-data"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.balanced_stein_data"), H("Actual Stein certificate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both standard Stein inequalities hold by exact algebraic equality for the stated matrices and weights."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("retained-order"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.retained_weight_larger"), H("The actual retained weight is larger"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For epsilon between zero and one, truncating the second coordinate retains the larger weight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("determinants-disagree"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.actual_determinants_disagree"), H("Persistent determinant-zero loss"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At z=4 the full state determinant is zero and the retained state determinant is minus one. This concerns det(I-zA), not an independently identified arithmetic or regularized determinant."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-error"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.actual_error_bound"), H("Consume the balanced error theorem"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing single-state truncation theorem gives the coefficient thirty-two epsilon squared divided by fifteen for the actual input-output trajectories."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arbitrary-accuracy-loss"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss.arbitrarily_small_error_with_determinant_loss"), H("Quantified failure of determinant preservation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive requested error coefficient, constructs a positive epsilon with bijective ports, ordered Stein data, a smaller certified error coefficient for every input window, and the same lost determinant zero. It does not refute exact minimal-realization uniqueness or a separately proved determinant identity."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/BalancedTruncationTail"))]));
}

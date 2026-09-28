using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class PredictiveEnergySplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the minimum-energy predictive lift, derive its dynamics and energy blocks, and prove that positive energy forces a nondegenerate even-dimensional visible Poisson form.",
        H("Predictive Energy Splitting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hamiltonian-covariance"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.hamiltonian_covariance"),
                H("Hamiltonian covariance identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A skew Poisson matrix and a symmetric invertible energy matrix give covariance skewness for the actual Hamiltonian generator."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lift-intertwines"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.lift_intertwines"),
                H("The constructed lift intertwines dynamics"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reduced covariance skewness and inverse covariance equations derive A L = L K. This equality is not assumed as a field of a certificate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lift-energy-blocks"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.lift_energy_blocks"),
                H("Energy orthogonality of visible and hidden coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every matrix R whose columns are in the observation kernel, the explicit lift has reduced Hessian Q and vanishing hidden energy cross terms."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hidden-projection"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.hidden_projection"),
                H("A dynamically invariant hidden projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The projection constructed as I-L O is idempotent, annihilates the visible lift, and commutes with the full generator."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-hessian"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.coordinate_hessian"),
                H("Block diagonal coordinate Hessian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual concatenated coordinate matrix has the claimed block Hessian. No Gaussian integration or volume Jacobian is inferred from this algebraic identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observation-powers"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.observation_powers"),
                H("All derivative orders respect the observation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Generator intertwining propagates to every natural power, not only the first derivative."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-lift-data"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.canonical_lift_data"),
                H("Construct inverses from positive energy and full row rank"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The witnesses are chosen as actual nonsingular inverses. Positive definiteness and injectivity of the observation transpose supply both inverse equations."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("predictive-poisson-nondegenerate"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PredictiveEnergySplitting.predictive_poisson_nondegenerate"),
                H("No radical under invariant positive energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reduced Poisson matrix times the transpose reduced generator is the Gram matrix of J times O-transpose. This proves invertibility of the reduced Poisson form and its even dimension. It does not construct an infinite-dimensional canonical commutation representation."))), DescribeRole.Theorem))));
}

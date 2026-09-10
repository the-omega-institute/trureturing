using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Cone;

internal sealed class UniformConeStabilityDocument : IScribeDocumentDefinition
{
    private const string P = "D5/S3/FluidDynamics/Cone/UniformConeStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every compact set of true-cone data admits one positive perturbation radius preserving the lower bound on v and positive definiteness of the cone matrix.",
        H("Uniform cone stability"), Blocks(
            Describe.Lean(DescribeId.Create("uniform-cone-stability-datum"),
                DeclarationHandle.Create(P + "ConeDatum"), H("Cone datum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A cone datum is a triple of real numbers in the order P, J, v, equipped with the product metric."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-cone-stability-true-cone"),
                DeclarationHandle.Create(P + "trueCone"), H("True cone"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The true cone consists of data for which v and P are greater than two and v is strictly below the cone bound at P and J."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-cone-stability-continuous-bound"),
                DeclarationHandle.Create(P + "continuous_coneBound"), H("Continuous cone bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cone bound is a continuous real function of the cone datum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-cone-stability-open-cone"),
                DeclarationHandle.Create(P + "isOpen_trueCone"), H("Open true cone"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The true cone is open in the space of cone data."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-cone-stability-compact-cone"),
                DeclarationHandle.Create(P + "compact_trueCone_stable"), H("Uniform perturbation radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every compact subset of the true cone admits a single positive radius such that any datum at distance at most that radius from any point of the subset remains in the true cone."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-cone-stability-positive-definite-matrix"),
                DeclarationHandle.Create(P + "compact_coneMatrix_posDef_stable"), H("Uniform matrix positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every compact subset of the true cone admits a single positive radius such that any datum at distance at most that radius from any point of the subset has v greater than two and a positive definite cone matrix."))),
                DescribeRole.Theorem))));
}

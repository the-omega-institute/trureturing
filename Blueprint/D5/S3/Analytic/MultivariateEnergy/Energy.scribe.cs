using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MultivariateEnergy;

internal sealed class EnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Energy of centered spherical matrix kernels.",
        H("Energy"), Blocks(
            Describe.Lean(DescribeId.Create("energy-family-moments"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Energy.energy_family_eq"),
                H("Cubic energy from the centered moment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite dimension d, real beta, and Borel probability measure mu on the unit sphere, put Q equal to the integral of xx transpose minus the identity divided by d. The three-input family has energy beta times tr(Q squared) minus tr(Q cubed). Fubini and integration of linear matrix functionals give the reduction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("averaged-family-pairing"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Energy.avgKernel_family_eq"),
                H("The averaged matrix pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In every positive dimension, integrating the first of the three inputs against normalized surface measure leaves beta divided by three times tr(A(x)A(y)). The surface average of A is zero, so both pairs involving the integrated input and the cubic term vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("averaged-family-positivity"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Energy.isCondPosDef_family"),
                H("Positivity for finite measure differences"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative beta the averaged kernel is conditionally positive definite. For any two finite Borel measures, its quadratic expression is beta divided by three times tr((Q1 minus Q2) squared). The moment matrices are real symmetric, so the trace is nonnegative. This proof does not need equality of the two total masses."))),
                DescribeRole.Theorem))));
}

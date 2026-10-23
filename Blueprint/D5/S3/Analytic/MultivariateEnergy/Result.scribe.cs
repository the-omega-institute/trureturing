using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MultivariateEnergy;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Result of centered spherical matrix kernels.",
        H("Result"), Blocks(
            Describe.Lean(DescribeId.Create("cubic-spherical-family-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Result.family_refutes"),
                H("A family of counterexamples"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In every dimension d at least three and for every beta strictly between zero and (d minus two) divided by d, the three-input kernel is continuous, symmetric, and invariant under all orthogonal transformations. Its averaged kernel is conditionally positive definite, but normalized surface measure does not minimize its energy. Surface measure has energy zero, while any Dirac probability measure has energy ((d minus one) divided by d) times (beta minus (d minus two) divided by d), which is negative."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("averaged-kernel-characterization-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Result.result"),
                H("Failure of the characterization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal equivalence between minimization by normalized surface measure and conditional positive definiteness of the averaged kernel is false. The family at dimension three, arity three, and beta equal to one tenth satisfies the latter property and violates the former. Orthogonal invariance includes invariance under rotations."))),
                DescribeRole.Theorem))));
}

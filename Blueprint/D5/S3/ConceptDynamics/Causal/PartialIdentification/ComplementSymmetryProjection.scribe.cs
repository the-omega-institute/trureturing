using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class ComplementSymmetryProjectionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/"
            + "ComplementSymmetryProjection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal averaging of a real parameter with its complement projects every "
            + "value to one half while erasing the antisymmetric centered defect.",
        H("Complement Symmetry Projection"),
        Blocks(
            Paragraph(Text(
                "The affine involution sends theta to one minus theta. Its unique fixed point is one half, and the centered defect theta minus one half changes sign under the involution.")),
            Paragraph(Text(
                "Equal averaging applies the invariant projection and therefore returns one half for every parameter, including off-center parameters. The projected value cannot identify whether the original parameter was fixed.")),
            Paragraph(Text(
                "For arbitrary stratum weight, the complementary query has slope two times the weight minus one. Parameter cancellation for every theta occurs exactly at equal weight.")),
            Describe.Lean(
                DescribeId.Create("complement-average-is-half"),
                DeclarationHandle.Create(Prefix + "symmetricAverage_eq_half"),
                H("Complementary symmetrization always equals one half"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity follows by exact affine cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetrization-does-not-identify-center"),
                DeclarationHandle.Create(
                    Prefix + "symmetric_average_does_not_identify_center"),
                H("The symmetric projection cannot identify the original center"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Zero is an explicit off-center parameter whose symmetrized query is still one half."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-weight-is-unique-cancellation"),
                DeclarationHandle.Create(
                    Prefix + "weightedComplementaryQuery_constant_half_iff"),
                H("Equal weight is exactly the parameter-cancelling regime"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating at zero proves necessity, while direct polynomial normalization proves sufficiency."))),
                DescribeRole.Theorem))));
}

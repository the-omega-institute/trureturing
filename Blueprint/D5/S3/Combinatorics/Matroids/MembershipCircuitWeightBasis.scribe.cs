using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class MembershipCircuitWeightBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral basis distinguishes petals on their zero-weight coordinates.",
        H("Weight Coordinates from Petal Membership"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("membership-separating-weight-basis"),
                DeclarationHandle.Create(Module + ".exists_membership_separating_weight_basis"),
                H("A simultaneous supported basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Keep a pivot outside every petal."
                    + " Partition the other indices by identical membership in the petals."
                    + " A supported integral basis concentrates the weights at one index of each class, preserves each petal span in both directions, and preserves the pivot line."
                    + " If every pair of petals differs on a class of size at least two, the petals have distinct intersections with the zero-weight indices outside the pivot."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PrivatePairCircuitWeightBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral basis preserves overlapping faces and separates their coefficients.",
        H("Weight Coordinates from Private Pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-private-pair-weight-basis"),
                DeclarationHandle.Create(Module + ".exists_private_pair_weight_basis"),
                H("Separating zero-weight coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the coordinate indices form a finite set and carry positive integer weights."
                    + " Fix a pivot outside every indexed face."
                    + " Suppose each face contains two distinct indices that are in no other face."
                    + " Partition the indices by membership in the faces and by equality to the pivot."
                    + " An integral change of basis concentrates the weights on one index per block and preserves each face span in both directions."
                    + " The pivot line is preserved."
                    + " Each private pair lies in one block, so at least one of its two indices has zero new weight."
                    + " The set of zero-weight indices outside the pivot therefore meets distinct faces in distinct subsets."))),
                DescribeRole.Theorem))));
}

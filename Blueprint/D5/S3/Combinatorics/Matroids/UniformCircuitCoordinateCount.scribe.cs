using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class UniformCircuitCoordinateCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subsets avoiding two elements.",
        H("Uniform Circuit Coordinate Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("card-avoid-both"),
                DeclarationHandle.Create(Module + ".card_avoid_both"),
                H("Subsets avoiding two elements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the two designated elements are distinct, the number of size-r subsets that avoid "
                    + "both is the binomial coefficient choosing r from the ground size minus two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("card-include-nonpivot"),
                DeclarationHandle.Create(Module + ".card_include_nonpivot"),
                H("Subsets containing the second element"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a size-(r + 1) subset avoids the first designated element and contains the second, "
                    + "deleting the second leaves a size-r subset of the complement of the two distinguished "
                    + "elements."))),
                DescribeRole.Theorem))));
}

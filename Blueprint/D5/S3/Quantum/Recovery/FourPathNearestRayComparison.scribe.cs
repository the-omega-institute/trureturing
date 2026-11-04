using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathNearestRayComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nearest-ray Kraus estimate separates trace-defect and coordinate-distance errors and preserves the source constants after finite summation.",
        H("Four-path nearest-ray comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-path-nearest-ray-error-aggregation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNearestRayComparison.finite_family_error_aggregation"),
                H("Finite-family error aggregation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite family of matrix errors K - B = E + F, if the squared norms of E and F are bounded by 2τ and c d² termwise, then the summed squared error is bounded by 4Στ + 2cΣd².")),
                    Paragraph(Text("The proof applies the squared triangle estimate pointwise and then distributes the finite sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-path-selected-mass-bounds-and-defect"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathNearestRayComparison.selected_mass_bounds_and_defect"),
                H("Selected mass bounds and defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For nonnegative coordinate weights with unit total mass, assigning each index to its larger coordinate yields selected masses in [0,1]. The two complementary masses sum to the finite sum of coordinatewise minima.")),
                    Paragraph(Text("The proof partitions each coordinate by the selected Boolean assignment and uses the completeness sums."))),
                DescribeRole.Theorem))));
}

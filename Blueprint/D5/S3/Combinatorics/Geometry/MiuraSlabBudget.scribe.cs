using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charging actual slab types to individual extremum cells", H("Charging actual slab types to individual extremum cells"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraslabbudget-neutralsupport"),
                DeclarationHandle.Create(Prefix + "neutralSupport"), H("Extrema with a neutral endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the union of the individual extremum cells in neutral row slabs and those in neutral column slabs. A cell in both sets remains one cell."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabbudget-neutral-slab-budget"),
                DeclarationHandle.Create(Prefix + "neutral_slab_budget"), H("Neutral vertex budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge array with at least two rows, the sum of the neutral row and column slab counts is at most the number of extrema with at least one neutral endpoint. Each neutral slab has two distinct incidences and each actual extremum has at most two neutral endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabbudget-neutral-budget-equality"),
                DeclarationHandle.Create(Prefix + "neutral_budget_equality"), H("Equality keeps both endpoints neutral"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the neutral support cardinality equals the total neutral row and column slab count, the row and column neutral supports coincide, and the two neutral slab counts are equal. Thus every extremum with one neutral endpoint has a neutral endpoint on the other axis too."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabbudget-matching-slab-budget"),
                DeclarationHandle.Create(Prefix + "matching_slab_budget"), H("Matching nonneutral rectangles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual unit-edge array with at least two rows and one column, the product of minimum row and column slab counts plus the analogous maximum product is at most the number of individual extrema outside the neutral support. Each rectangle supplies a minimum or maximum, distinct rectangles give distinct cells by actual slab uniqueness, and minimum and maximum witnesses cannot coincide."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabbudget-equality"),
                DeclarationHandle.Create(Prefix + "slab_budget_equality"), H("Equality excludes a single neutral endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the total individual extremum count equals the sum of the two neutral slab counts and the two matching-type products, every extremum incident with a neutral row slab is incident with a neutral column slab and conversely. The two neutral slab counts are equal. This is a consequence of saturation of the actual charge; it does not by itself classify geometric equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabbudget-slab-extremum-budget"),
                DeclarationHandle.Create(Prefix + "slab_extremum_budget"), H("Full actual slab charge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual unit-edge array with at least two rows and one column, its total individual extremum count is at least the sum of its two neutral slab counts, the product of its minimum row and column slab counts, and the product of its maximum row and column slab counts. These are canonical interval families of the same array, with no independent incidence graph supplied."))), DescribeRole.Theorem))));
}

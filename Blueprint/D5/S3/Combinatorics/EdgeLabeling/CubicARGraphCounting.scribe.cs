using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CubicARGraphCounting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite partial-injection extension counts and the counting union bound.",
        H("Counting cubic AR-labelings"),
        Blocks(
            Node("nat_card_equiv_constraints", "Indexed constraints without a chosen enumeration",
                "The indexed extension count also holds for the natural cardinality of the "
                + "constraint subtype, independently of its chosen finite enumeration."),
            Node("exists_avoiding_of_sum_card_lt", "An outcome avoiding every bad event",
                "If the sum of the cardinalities of a finite family of bad events is smaller "
                + "than the cardinality of the finite sample space, an outcome lies in none "
                + "of the bad events. This follows from the cardinality bound for a finite union.")),
        []));

    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("cubic-ar-counting-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}

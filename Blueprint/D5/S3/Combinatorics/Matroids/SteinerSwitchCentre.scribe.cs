using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerSwitchCentreDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerSwitchCentre";
    private static readonly LibraryNoteRef Loop = LibraryNoteRef.Create("D5/L/FiniteGeometry/quackenbush1976steinerloops");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centre of the Steiner loop determines which deletions admit a maximal switch.",
        H("Central Points and Point-Deleted Steiner Switches"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("steiner-product"),
                DeclarationHandle.Create(Module + ".steinerMul"),
                H("Product in the Steiner loop"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Loop),
                Blocks(Paragraph(Text("Adjoin an identity to a finite complete Steiner triple system. Left multiplication by an original point is its matching translation. Left multiplication by the identity leaves every point fixed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("deletions-admitting-switches"),
                DeclarationHandle.Create(Module + ".AdmitsSwitch"),
                H("A deletion that admits a switch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A deleted point admits a switch if the retained packing has a map whose partners are exactly its uncovered pairs and if some retained pivot and start satisfy the successful-switch predicate for that map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("switches-detect-noncentrality"),
                DeclarationHandle.Create(Module + ".admits_switch_iff_not_central"),
                H("Maximal switches detect noncentral points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In a finite complete Steiner triple system on r+1 points, deleting an original point admits a maximal switch exactly when that point lies outside the centre of its Steiner loop. Centrality means commuting with every element and satisfying both the left and right association laws.")),
                    Paragraph(Text("At an eligible start, the switch fails exactly when the two translations commute there. The adjoined identity, the deleted point, a retained pivot and the third point of their block form a commuting square. Together these cases show that failure at every retained pivot gives commutation on the whole carrier. In the commutative loop, interchanging the other two inputs converts this condition into the association laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("number-of-deletions-admitting-switches"),
                DeclarationHandle.Create(Module + ".ncard_admits_switch"),
                H("Counting the deletions that admit a switch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In a finite complete Steiner triple system on r+1 points, the number of deleted points with some successful switch is r+2 minus the cardinality of the Steiner loop centre.")),
                    Paragraph(Text("The original points admitting a switch embed onto the complement of the centre. The only adjoined point is the identity, which lies in the centre."))),
                DescribeRole.Theorem))));
}

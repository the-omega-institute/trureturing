using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class OrderedGridMemoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core branching, exact certificates and their precise scope.",
        H("OrderedGridMemory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-point"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.Point"),
                H("Square-grid coordinates"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pairs of integers describe actual grid vertices in the frame of an east-facing incoming edge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-direction"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.direction"),
                H("The three forward directions"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three directions are straight, right and left. The fourth direction is the already-deleted parent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-position"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.position"),
                H("All six local orderings"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The six rows specify the permutations SRL, SLR, RSL, RLS, LSR and LRS."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-deleted"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.deleted"),
                H("Ordered vertex deletions"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Before following a child, delete the current vertex and all earlier neighbors. Including an already absent neighbor does not change the remaining domain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-recenter"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter"),
                H("Normalize the chosen incoming heading"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An integer translation and quarter-turn put the child at the origin and its incoming heading east."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-recenter-injective"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter_injective"),
                H("Coordinate normalization preserves identity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of the recentered vertices implies equality of both original integer coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-advance"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance"),
                H("The actual remaining finite domain"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Delete vertices in the prescribed order and apply the same coordinate normalization to all remaining vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-memorystep"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.memoryStep"),
                H("Truncated geometric blockers"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Update the actual blocked set and retain only points within a Manhattan disk. Forgotten blockers are discarded permanently."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-advance-disjoint-memorystep"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance_disjoint_memoryStep"),
                H("Geometric soundness for every radius"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Disjointness between available vertices and recorded blockers is preserved by deletion, recentering and truncation. The proof uses injectivity of the actual coordinate map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-orderedcount"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount"),
                H("Count actual domain paths"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A child is available exactly when its grid vertex belongs to the actual finite domain. Missing table entries use a fallback state and never suppress an available child by definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-orderedgridmemory-orderedcount-le-pathcount"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount_le_pathCount"),
                H("Uniform finite-domain simulation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact table rejection and geometric-successor identities imply domination of every finite-domain path count at every depth. RadiusThreeCertificates proves these finite obligations for its concrete table."))),
                DescribeRole.Theorem),
            Paragraph(Text("The sources were logically reviewed and the concrete certificates independently replayed using exact integers. Lean elaboration, axiom-print execution and Scribe emission were not performed in the authoring runtime. These candidate sources do not assert an improved global zero-free threshold.")))));
}

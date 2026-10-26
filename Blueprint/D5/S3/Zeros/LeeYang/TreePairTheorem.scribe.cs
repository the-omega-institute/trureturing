using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class TreePairTheoremDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete arbitrary finite tree physical pair coefficient theorem.", H("The complete arbitrary finite tree physical pair coefficient theorem."),
        Blocks(Paragraph(Text("The grouped single-vertex coefficient is d_v^2(d_v^2-1)/24. Its double sum uses ordered distinct receiving vertices with factor one half, equivalently unordered distinct pairs of coefficient d_u*d_v*(d_u*d_v-A_uv)/9. The exact receiving-incidence identity connects it to the complete allocation polynomial. The root argument uses positivity, the constrained quadratic identity and reciprocity. It asserts neither stability of an individual placement nor simplicity of the remaining roots. One fixed finite simple connected acyclic tree has at least two edges. The existing NamedSpanningTree src tgt Set.univ interface retains every edge; source incidence degree equals actual graph degree. The automorphism divisor is the cardinality of actual graph self-isomorphisms and is nonzero. The literal all-vertex formal coefficient has exact degree 2e+2, every complex root has norm one, and root one has multiplicity exactly the odd-degree vertex count. The quotient degree is N-h, and its roots avoid both endpoints. Zero, minus one and projective infinity are excluded. The full binary source is the homogenization and uses the same coupling ratio. This does not resolve the whole Fiol conjecture, other total multisets or tau values, arbitrary positive rho, a sum across trees, or root simplicity.")),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-receivingPairCount-add"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.receivingPairCount_add"),
                H("Receivingpaircount add"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-sum-by-receivers"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.sum_by_receivers"),
                H("Sum by receivers"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-grouped-cayley"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.grouped_cayley"),
                H("Grouped cayley"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-treeAllocation-grouped"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_grouped"),
                H("Treeallocation grouped"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-treeAllocation-disk-nonzero"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_disk_nonzero"),
                H("Treeallocation disk nonzero"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-treeAllocation-unit-circle"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_unit_circle"),
                H("Treeallocation unit circle"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-treeAllocation-neg-one-pos"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.treeAllocation_neg_one_pos"),
                H("Treeallocation neg one pos"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-named-tree-card-vertices"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_card_vertices"),
                H("Named tree card vertices"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-named-tree-source-degree"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_source_degree"),
                H("Named tree source degree"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-named-tree-degree-positive"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.named_tree_degree_positive"),
                H("Named tree degree positive"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-complete-named-tree-pair"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairTheorem.complete_named_tree_pair"),
                H("Complete named tree pair"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Theorem))));
}

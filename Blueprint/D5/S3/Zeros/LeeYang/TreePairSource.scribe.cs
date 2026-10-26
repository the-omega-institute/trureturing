using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class TreePairSourceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal generator coefficient extraction and the exact physical scalar.", H("Formal generator coefficient extraction and the exact physical scalar."),
        Blocks(Paragraph(Text("The formal generator monomial is Z_5^2 Z_3^(e-2). For every cutoff M at least three, its coefficient forces exactly two distinct edges to have total three and every other edge total two. The literal all-vertex equation (2.19) supplies the factorial, binomial, degree-parity and automorphism factors. Equation (2.31) literally prints m, whereas (2.19) prints m+1; no erratum or authorial intent is inferred. The split and Boolean endpoint choices are in bijection. A selected two-edge set has all four endpoint choices, and the receiving increments sum to two. The source coefficient equals C_T times the complete allocation polynomial; its exact scalar is 50*(-1)^e*12^e*product_v(d_v-1)!/aut. The aut parameter here is instantiated by the actual graph automorphism order in TreePairTheorem. Variable zero is the dimensionless second coupling, and variable one is the first. The source binary vertex contains lambda1^M+(-1)^degree*lambda2^M and all original factorial factors. The proof uses the total incident mass 2e+2 and canonical homogenization of finite sums and products. The full source bridge is derived, not assumed.")),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-formal-pair-coefficient"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.formal_pair_coefficient"),
                H("Formal pair coefficient"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-source-scalar"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.source_scalar"),
                H("Source scalar"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-sourceMass-total"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.sourceMass_total"),
                H("Sourcemass total"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-sum-ordered-distinct-twice"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.sum_ordered_distinct_twice"),
                H("Sum ordered distinct twice"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-sum-sourceSplits"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.sum_sourceSplits"),
                H("Sum sourcesplits"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-receivedCount-pairChoice"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.receivedCount_pairChoice"),
                H("Receivedcount pairchoice"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-exact-source-coefficient"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.exact_source_coefficient"),
                H("Exact source coefficient"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-treeAllocation-degree-multiplicity"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.treeAllocation_degree_multiplicity"),
                H("Treeallocation degree multiplicity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-full-source-coefficient-homogenize"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.full_source_coefficient_homogenize"),
                H("Full source coefficient homogenize"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-exact-full-source-coefficient"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairSource.exact_full_source_coefficient"),
                H("Exact full source coefficient"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Theorem))));
}

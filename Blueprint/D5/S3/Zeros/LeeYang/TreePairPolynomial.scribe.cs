using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class TreePairPolynomialDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive allocation sums have exact degree and endpoint multiplicity.", H("Positive allocation sums have exact degree and endpoint multiplicity."),
        Blocks(Paragraph(Text("The hypotheses quantify over arbitrary finite allocation types, positive degrees and weights, a common total mass and even degree sum. No coefficient cancellation is assumed. Every odd-degree vertex contributes one factor 1-X; the quotient has strictly positive value at one. Reciprocity transfers open-disk exclusion to the exterior. Homogenization uses the canonical Mathlib polynomial construction.")),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-allocation-degree-and-leading"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairPolynomial.allocation_degree_and_leading"),
                H("Allocation degree and leading"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-allocation-multiplicity-one"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairPolynomial.allocation_multiplicity_one"),
                H("Allocation multiplicity one"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-allocation-roots-on-circle"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairPolynomial.allocation_roots_on_circle"),
                H("Allocation roots on circle"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-allocation-quotient-degree"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairPolynomial.allocation_quotient_degree"),
                H("Allocation quotient degree"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-homogenize-complex-eval"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairPolynomial.homogenize_complex_eval"),
                H("Homogenize complex eval"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-homogenize-complex-infinity"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairPolynomial.homogenize_complex_infinity"),
                H("Homogenize complex infinity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Theorem))));
}

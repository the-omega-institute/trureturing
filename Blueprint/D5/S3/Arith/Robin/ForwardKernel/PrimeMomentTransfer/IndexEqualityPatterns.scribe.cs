using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class IndexEqualityPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical equality-pattern decompositions of finite index sums",
        H("Index equality patterns"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-index-pattern-sum"), DeclarationHandle.Create(Prefix + "patternSum"), H("Four-index pattern sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum a function over injective representative tuples after composing with a prescribed map from four positions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-index-pattern-sum"), DeclarationHandle.Create(Prefix + "patternSum3"), H("Three-index pattern sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum a function over injective representative tuples after composing with a prescribed map from three positions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sum-fin-three-eq-pattern-sums"), DeclarationHandle.Create(Prefix + "sum_fin_three_eq_pattern_sums"), H("Three-index equality classification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every sum over triples decomposes into the five canonical patterns: three distinct indices, each of the three two-equal patterns, and one common index."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-fin-four-eq-pattern-sums"), DeclarationHandle.Create(Prefix + "sum_fin_four_eq_pattern_sums"), H("Four-index equality classification"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every sum over quadruples decomposes into the fifteen canonical equality patterns, grouped by multiplicities 1+1+1+1, 2+1+1, 2+2, 3+1, and 4."))), DescribeRole.Theorem))));
}

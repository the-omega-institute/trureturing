using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class LacunaryProgressionSubshiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact lacunary progression subshifts", H("Compact lacunary progression subshifts"), Blocks(
        Paragraph(Text("For m>=3, X_m is the binary two-sided subshift in which no three distinct vertices of any m-term progression of step (m+1)^k can all equal one. Equivalently, every such progression contains at most two ones. The inherited compatible countable-product metric is used throughout.")),
        Describe.Lean(DescribeId.Create("lacunary-legal-closed"), DeclarationHandle.Create(Owner + "lacunary_legal_closed"), H("Closed configuration space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Each forbidden triple is a finite open cylinder. The intersection of their closed complements is closed in the compact binary product."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lacunary-legal-shift"), DeclarationHandle.Create(Owner + "lacunary_legal_shift"), H("Integer-translation invariance"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Translating a progression only changes its starting coordinate, so every integer shift preserves the exact constraint."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lacunary-legal-of-subsingleton-support"), DeclarationHandle.Create(Owner + "lacunary_legal_of_subsingleton_support"), H("Sparse legal points"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A support of cardinality at most one cannot contain a forbidden triple. The positivity of the progression step separates its distinct vertices."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lacunary-zero-legal"), DeclarationHandle.Create(Owner + "lacunary_zero_legal"), H("The zero configuration"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The all-zero point belongs to every X_m and witnesses nonemptiness."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lacunary-shift-continuous"), DeclarationHandle.Create(Owner + "lacunary_shift_continuous"), H("Continuity of the shift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The map is the restriction of the genuine full-shift map by one. The closed invariant carrier is compact."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lacunary-shift-iterate"), DeclarationHandle.Create(Owner + "lacunary_shift_iterate"), H("Natural-time coordinate formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The i-fold iterate reads coordinate i+j of the original two-sided configuration. Pseudo-orbit time is natural while symbol coordinates are integers."))), DescribeRole.Theorem))));
}

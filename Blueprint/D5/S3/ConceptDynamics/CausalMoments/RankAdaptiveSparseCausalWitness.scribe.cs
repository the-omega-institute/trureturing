using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class RankAdaptiveSparseCausalWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The checked affine presentation preserves the original causal constraint system and target with a smaller support budget. Separate residual certificates control decisions for queries outside the retained family.",
        H("Affine-budget causal witnesses and robust query decisions"),
        Blocks(
            Describe.Lean(DescribeId.Create("affine-causal-witness"),
                DeclarationHandle.Create(Prefix + "checked_affine_causal_witness"), H("Original-carrier witness with reduced support budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Acceptance reconstructs all original rows and the target, packages the computed result as FiniteResponseLaw and bounds its support by the selected coordinate count plus one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-lower-endpoint"),
                DeclarationHandle.Create(Prefix + "checked_affine_lower_endpoint"), H("Preserve the exact lower endpoint and its dual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing lower dual certificate is reused with the smaller checked primal witness. No inequality or objective coefficient is altered."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("compressed-query-decision"),
                DeclarationHandle.Create(Prefix + "checked_compressed_query_decision"), H("Transfer a strict decision with a certified margin"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the compressed query exceeds the threshold by more than the checked residual width, the original query also exceeds it. The bound concerns finite model approximation, not sampling uncertainty."))), DescribeRole.Theorem))));
}

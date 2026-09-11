using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class GeneratedProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Archive-Preserving Generated Product.",
        H("Archive-Preserving Generated Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("generatedproduct-product"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product"),
                H("Only generated pairs are current or selected"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The archive retains the two tagged old archives and every pair of current parents under "
                    + "the third tag. All generated candidate pairs form the new current region. Selection uses "
                    + "only selected parent pairs; old events never contribute again merely by being archived."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("generatedproduct-q-product"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.q_product"),
                H("Selected and background sums multiply exactly"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected readout is the actual signed double sum and equals the product of input "
                    + "readouts. The same calculation on full current regions gives the background product and "
                    + "balanced closure. The archive has E-left plus E-right plus Omega-left times Omega-right "
                    + "events."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("generatedproduct-embeddingleft"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.embeddingLeft"),
                H("Both old archives embed with all attributes and order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit tagged injections preserve all four attributes and preserve and reflect old "
                    + "causality. The path invariant and frozen path-mapping theorem occur on the proof path. "
                    + "No nonzero-readout or nonempty-current assumption is needed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("generatedproduct-causal-iff-bounded-path"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.causal_iff_bounded_path"),
                H("HF causality has the required finite path semantics"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The transported causal relation equals actual TransGen of the two copied relations and "
                    + "the two parent edges on HF members. Its paths are characterized by positive "
                    + "relation-series lengths bounded by archive cardinality minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("generatedproduct-product-eq-of-empty-right"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product_eq_of_empty_right"),
                H("Archive retention does not recover old selections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two selections on each fixed input context, an empty opposite current region makes "
                    + "the product results equal. The symmetric theorem handles an empty left region. The "
                    + "result retains old archives, without claiming recovery of prior selections or current "
                    + "regions."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class ProductNodesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generated Product Events.",
        H("Generated Product Events"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("productnodes-generatedattributes"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ProductNodes.generatedAttributes"),
                H("Attributes come from the two actual parents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Generated time is the maximum of the two parent times plus one. Position is their sum, "
                    + "the Boolean sign represents the product of signed contributions, and the source is the "
                    + "ordered FreeMagma pair. Old attributes are copied verbatim."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("productnodes-eventcode-injective"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ProductNodes.eventCode_injective"),
                H("The three literal tags separate all occurrences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The presentation includes both complete old archives and every pair of current parents. "
                    + "Tag two carries the literal HF pair of the two event names. The proved injection and "
                    + "finite presentation equivalence make this the prescribed HF archive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("productnodes-source-code-generated"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ProductNodes.source_code_generated"),
                H("Source coding commutes with ordered tree pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing source encoder represents the generated tree by its branch tag and ordered "
                    + "pair of source codes. Event tags do not rename natural leaves. The HF event code also "
                    + "commutes with the fixed set-theoretic pairing."))),
                DescribeRole.Theorem))));
}

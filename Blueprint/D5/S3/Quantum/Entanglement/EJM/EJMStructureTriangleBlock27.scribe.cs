using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMStructureTriangleBlock27Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual structural checks for one original EJM row interval.",
        H("Actual triangle structural row interval 34816 to 35840"),
        Blocks(
            Paragraph(Text("This module checks every original triangle row with index at least 34816 and below 35840. Each split retains all four actual values, earlier child indices, stored lower inequalities and full partial-assignment symmetry transport. Terminal rows retain exact completed events. Only kernel checkpoint boundaries change.")),
            Describe.Lean(DescribeId.Create("accepted-interval"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EJM/EJMStructureTriangleBlock27.accepted"),
                H("The whole original row interval passes its exact structural check"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The receipt covers the entire interval and is consumed by EJMStructureCertificates. It supplies structural checks only; terminal score bounds, complete global acceptance and nonlocality require their separate full proofs."))),
                DescribeRole.Theorem))));
}

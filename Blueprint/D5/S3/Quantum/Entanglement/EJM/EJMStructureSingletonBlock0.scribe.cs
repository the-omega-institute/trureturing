using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMStructureSingletonBlock0Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual structural checks for one original EJM row interval.",
        H("Actual singleton structural row interval 0 to 4096"),
        Blocks(
            Paragraph(Text("This module checks every original singleton row with index at least 0 and below 4096. Each split retains all four actual values, earlier child indices, stored lower inequalities and full partial-assignment symmetry transport. Terminal rows retain exact completed events. The split changes kernel checkpoint boundaries while preserving every original obligation.")),
            Describe.Lean(DescribeId.Create("accepted-interval"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EJM/EJMStructureSingletonBlock0.accepted"),
                H("The whole original row interval passes its exact structural check"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The receipt quantifies over the entire finite interval and is consumed by EJMStructureCertificates. It supplies structural checks only; terminal score bounds, global search acceptance and nonlocality require their separate full proofs."))),
                DescribeRole.Theorem))));
}

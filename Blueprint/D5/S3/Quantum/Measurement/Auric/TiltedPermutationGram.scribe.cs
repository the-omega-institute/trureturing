using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class TiltedPermutationGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent Choi block after relabeling",
        H("Coherent Choi block after relabeling"),
        Blocks(Describe.Lean(
            DescribeId.Create("averaged-coherent-block"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/TiltedPermutationGram.averaged_coherent_block"),
            H("Coherent Choi block after relabeling"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Sector exchange with flag exchange and pair transposition average the coherent terms into the explicit three-coordinate Gram matrix."))),
            DescribeRole.Theorem))));
}

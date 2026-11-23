using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzPhysicalMarginalMismatchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive mismatch in the retained marginal.",
        H("Positive mismatch in the retained marginal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("physical-marginal-mismatch"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PetzPhysicalMarginalMismatch.physical_marginal_mismatch"),
                H("Uniform lower bound at positive reference spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing the signed flag coherences yields the retained-source minus recovered-marginal derivative. Its real off-diagonal entry is at least ε²/10 for every positive η in the stated t and ε ranges."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class AnchorMUBNormalFormHadamardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Hadamard classification in dimensions two and three.",
        H("Complex Hadamard classification in dimensions two and three"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-anchormubnormalformhadamard-flat-two-equivalent"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_two_equivalent"),
                H("Qubit flat unitaries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rescale the entry moduli to one and dephase the first row and column. Orthogonality determines the remaining entry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-anchormubnormalformhadamard-flat-three-equivalent"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_three_equivalent"),
                H("Qutrit flat unitaries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A dephased row of length three orthogonal to the all-ones row has the two nontrivial cube roots of unity in its last entries. Orthogonality forces the two rows to use opposite orders."))), DescribeRole.Theorem))));
}

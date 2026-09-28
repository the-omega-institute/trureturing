using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FiniteLocalRecoveryObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For normalized common-label source families whose local rank-one projectors span every local Hermitian matrix space, an orthogonal pair at one holder rules out exact all-matrix recovery by any finite local protocol. The protocol permits arbitrary independent mixed local ancillas, adaptive coarse completely positive instruments, changing finite memories, repeated visits, zero branches and early leaves, with system unitary feedback only at termination. Scalar leaf maps and label-independent prefix weights are derived from recovery, not assumed.",
        H("FiniteLocalRecoveryObstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-informationally-complete-obstruction"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FiniteLocalRecoveryObstruction.actual_informationally_complete_obstruction"),
            H("finite local recovery obstruction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For normalized common-label source families whose local rank-one projectors span every local Hermitian matrix space, an orthogonal pair at one holder rules out exact all-matrix recovery by any finite local protocol. The protocol permits arbitrary independent mixed local ancillas, adaptive coarse completely positive instruments, changing finite memories, repeated visits, zero branches and early leaves, with system unitary feedback only at termination. Scalar leaf maps and label-independent prefix weights are derived from recovery, not assumed."))),
            DescribeRole.Theorem))));
}

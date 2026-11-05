using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class PositiveRefinementCornerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive maps dominated by a projection compression have one scalar on the entire corner.",
        H("PositiveRefinementCorner"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("corner-dominated-scalar"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/PositiveRefinementCorner.corner_dominated_scalar"),
                H("Scalar rigidity on an arbitrary projection corner"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite decidable coordinate type n, every Hermitian idempotent P in M_n(C), and every complex linear endomorphism Phi that is positive on every PSD input and satisfies Phi(X) at most P X P on those inputs, there is a real c in [0,1] with Phi(X)=c P X P for every complex X. The zero projection and empty coordinate types are included. A spectral frame identifies the actual support corner with M_r(C). Ordinary positivity removes the input cross terms, while domination restricts the output to the same corner. The identity domination theorem on this corner supplies the common scalar. Complete positivity and a Kraus form of Phi are conclusions of applications, never assumptions here."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FibonacciQutritSpectralTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A small null-reference loss forces strict rank-two improvement in the Fibonacci qutrit.",
        H("Fibonacci qutrit spectral transport"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-spectral-transport"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Divergence/FibonacciQutritSpectralTransport.strict_spectral_transport"),
            H("Strict rank-two improvement"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/mathlib2026schurcomplement")),
            Blocks(
                Paragraph(Text(
                    "Take a positive definite qutrit reference C and a trace-one comparison A "
                    + "with 4C/3 ≤ A ≤ 7C/3. Let ρ be a trace-one positive semidefinite null "
                    + "state. Assume c = Re Tr C ≥ 11/19, e ≥ c/3 and "
                    + "Re Tr A[log(C + eρ) − log C] ≤ 1/114.")),
                Paragraph(Text(
                    "A floor C ≥ I/500 would force a loss greater than "
                    + "(4/3)(1/500) log 64 ≥ 4/375. Hence the smallest eigenvalue λ lies in "
                    + "(0, 1/500). Conjugate by a unitary eigenbasis and move a λ-coordinate "
                    + "to the ray. Functional calculus and cyclicity of trace preserve the "
                    + "original divergence in these coordinates.")),
                Paragraph(Text(
                    "Let E be this coordinate change, Cₚ the retained principal block of EC, "
                    + "and τ = Cₚ/Tr Cₚ. Compress a block matrix by adding its ray mass times τ "
                    + "to its retained principal block. The compressed A and positive reference C "
                    + "are positive semidefinite, retain their respective traces, and have rank "
                    + "at most two. Adding e times the freed ray projection to the compressed C "
                    + "gives a positive definite reference and a strictly larger Umegaki "
                    + "divergence than the original pair.")),
                Paragraph(Text(
                    "The same real-linear compression sends each positive source preparation "
                    + "to a trace-one positive semidefinite matrix supported on the retained "
                    + "qubit. It distributes over each finite weighted sum with its original "
                    + "weights. The null preparation becomes the trace-one projection onto "
                    + "the freed ray."))),
            DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class FramedCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Framed Coefficient", H("Framed Coefficient"),
        Blocks(
            Paragraph(Text("Hilbert-Schmidt estimates, matrix logarithm and integrated Jacobi formula near the identity. Lagrange's identity for the top coefficient, with weights at decreasing integer nodes. Transport of the coefficient, its measure and product formula through a frame to U(J).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/FramedCoefficient.isIdempotentKernel_psiInFrame"),
                H("isIdempotentKernel_psiInFrame"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let l = 2λ have gap 500n³+A for ε, n ≥ 1, J a hermitian involution, p invertible with p*Jp = diag(ε). Then g ↦ deg_λ·ψ_λ(p⁻¹gp) is a kernel (IsIdempotentKernel) on U(J) for the compact dual measure.")))))));
}

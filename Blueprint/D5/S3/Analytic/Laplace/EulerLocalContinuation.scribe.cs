using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class EulerLocalContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex local continuation for an Euler differential equation.",
        H("Euler Local Continuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("euler-local-continuation-ordinary"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerLocalContinuation.exists_extension_of_ne_zero"),
                H("Continuation at a nonzero real center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let c be a nonzero real number and r a positive radius. Let R be holomorphic on the complex disk of center c and radius r, and F holomorphic on its right half, defined by Re(z)>c. If z F''(z)+2 F'(z)=R(z) throughout that complex half disk, then some positive radius delta at most r admits a holomorphic function H on the full disk of radius delta, with H=F throughout its right half.")),
                    Paragraph(Text("Choose two successive complex primitives Q and P of R on the original disk. The equation implies that F+z F'-Q has zero derivative. Connectedness of the complex half disk makes it a constant A. A second integration gives zF-P=Az+B throughout that same half disk. Shrinking the full disk to avoid zero makes (P+Az+B)/z the desired holomorphic extension. No bound on the derivatives of F is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-local-continuation-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerLocalContinuation.exists_extension_at_zero"),
                H("A finite boundary value at the singular center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let r>0, with R holomorphic on the full disk of radius r about zero and F holomorphic on its complex right half. Suppose z F''+2 F'=R there. If F(x) tends to a finite complex value ell as positive real x tends to zero, then F extends to a holomorphic function H on a smaller full complex disk. It agrees with F on the entire right half disk and satisfies H(0)=ell.")),
                    Paragraph(Text("Normalize the first primitive by Q(0)=ell and the second by P(0)=0. The same complex uniqueness argument gives zF-P=Az+B. Taylor factorization of the actual primitive P gives P=zH near zero, with H holomorphic and H(0)=P'(0)=ell. Along the positive real axis, the finite limit first forces B=0. Complex agreement then has the form F=H+A throughout the half disk. Taking the boundary limit again forces A=0.")),
                    Paragraph(Text("The finite limit is essential: the homogeneous solution 1/z has a pole at zero. These local statements do not establish global convergence of a signed Laplace transform, a zero exclusion for zeta, Robin's inequality, or the Riemann hypothesis. The complex primitive and Taylor principles are classical; no literature originality is asserted."))),
                DescribeRole.Theorem))));
}

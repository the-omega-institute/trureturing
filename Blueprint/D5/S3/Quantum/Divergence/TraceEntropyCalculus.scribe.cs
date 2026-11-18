using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class TraceEntropyCalculusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strong Klein remainder gives a two-sided chain rule for noncommuting matrix entropy.",
        H("Differentiating finite-matrix trace entropy"), Blocks(
            Describe.Lean(
                DescribeId.Create("has-deriv-at-trace-mul-log"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/TraceEntropyCalculus.hasDerivAt_trace_mul_log"),
                H("A derivative without differentiating eigenvectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let X be a real-parameter curve of complex square matrices on any "
                    + "finite index type, including the empty type. Suppose X has derivative V at t0, "
                    + "X(t0) is positive definite, and X(t) is Hermitian throughout some neighbourhood "
                    + "of t0. In the L2 operator norm, the real function Re Tr(X(t) log X(t)) has "
                    + "derivative Re Tr(V(log X(t0)+I)). The trace is unnormalized. There is no trace-one "
                    + "condition and no commutation condition between matrices at different times.")),
                    Paragraph(Text("A positive spectral floor at X(t0), together with the selfadjoint "
                    + "norm-order bounds, gives local positive definiteness. Continuity gives one common "
                    + "spectral ceiling for X(t0) and the nearby matrices. Applying the existing strong "
                    + "Klein inequality in both orders places the tangent remainder R between zero and "
                    + "Re Tr((X(t)-X(t0))(log X(t)-log X(t0))). The unequal-trace corrections supply "
                    + "the identity matrix in the derivative.")),
                    Paragraph(Text("The matrix difference quotient converges to V, while continuity of "
                    + "CFC log on selfadjoint units makes the logarithm increment tend to zero. The norm "
                    + "of the normalized remainder is bounded by the norm of their trace product. "
                    + "This proves convergence to zero for both signs of t-t0. The argument neither "
                    + "divides an order inequality by a signed time increment nor assumes a derivative "
                    + "of the matrix logarithm. At an empty index type all traces vanish.")),
                    Paragraph(Text("For a fixed positive definite reference tau, subtracting the "
                    + "linear function Re Tr(X(t) log tau) gives the derivative of the finite relative "
                    + "entropy expression. The amplified Pauli flow uses this rule with V=-L(X); "
                    + "trace preservation removes the identity term, and its fixed memory reference "
                    + "removes the log tau pairing. The local chain rule alone is not a global entropy "
                    + "inequality or a singular endpoint limit."))),
                DescribeRole.Theorem))));
}

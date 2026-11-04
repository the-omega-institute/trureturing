using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfCubicRadialDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfCubicRadial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp cubic compatibility for arbitrary finite Hermitian matrix pencils with a radial denominator.",
        H("Cubic radial trace compatibility"),
        Blocks(
            Entry("cubicRadialTrace", "The rational trace function",
                "For complex matrices A and B and real k, define "
                + "f(t)=Re Tr((A+tB)^3)/(1+kt)^2. This is the actual scalar function, "
                + "with its usual real derivatives. Its denominator is nonzero on a neighborhood of zero.",
                DescribeRole.Definition),
            Entry("cubic_derivatives", "Second and third derivatives",
                "For every finite index type, arbitrary complex square matrices A and B, and real k, "
                + "put E=B-kA. Then f''(0)=6 Re Tr(A E^2) and "
                + "f'''(0)=6 Re Tr((B-4kA) E^2). No Hermitian or positivity hypotheses "
                + "are needed for these identities. Expanding the cubic and using cyclicity of "
                + "trace gives a scalar cubic numerator. Repeated quotient differentiation near "
                + "zero proves the identities for iteratedDeriv, including differentiability "
                + "on the neighborhood where the denominator is nonzero.", DescribeRole.Theorem),
            Entry("cubic_radial_compatibility", "The noncommutative cubic estimate",
                "For every finite index type, Hermitian A and B with A+B and A-B positive "
                + "semidefinite, and every real k, one has f''(0)>=0 and "
                + "|f'''(0)|<=(1+4|k|)f''(0). Thus |k|<=1 gives the constant 5. "
                + "The assumptions already imply that A is positive semidefinite. They allow "
                + "a singular center, singular endpoints, the empty index type, and zero Hessian; "
                + "in the last case the third derivative is zero. A and B need not commute. "
                + "Indeed, the congruences E(A+B)E and E(A-B)E are positive semidefinite. "
                + "Trace cyclicity gives |Re Tr(B E^2)|<=Re Tr(A E^2), "
                + "and the derivative formulas and the triangle inequality give the result.",
                DescribeRole.Theorem),
            Entry("UniversalCubicBound", "A dimension independent constant",
                "UniversalCubicBound(C) means that for every natural dimension m, PSD A, "
                + "Hermitian B, PSD endpoints A+B and A-B, and real |k|<=1, "
                + "the actual derivatives obey |f'''(0)|<=C f''(0).",
                DescribeRole.Definition),
            Entry("universal_constant_iff", "The sharp uniform constant",
                "For every real C, UniversalCubicBound(C) holds if and only if C>=5. "
                + "Sufficiency follows from the general matrix estimate. Necessity already "
                + "follows in dimension one from A=1, B=-1, k=1, for which the Hessian "
                + "is 24 and the third derivative is -120. The center is positive definite "
                + "and one endpoint is singular. Consequently 5 cannot be improved even "
                + "if the class is restricted to positive definite centers.", DescribeRole.Theorem),
            Paragraph(Text("This is the normalized matrix-pencil result for alpha=3 and the "
                + "radial second-variable restriction of the He-Saunderson-Fawzi question, "
                + "Operator convexity along lines, self-concordance, and sandwiched Renyi entropies: "
                + "arXiv:2502.05627v1, Conjecture 6.2; DOI 10.1007/s10107-025-02314-0, "
                + "Conjecture 1. "
                + "General second-variable directions and other exponents remain outside "
                + "this theorem. The full conjecture remains open.")),
            Paragraph(Text("Application to the physical radial trace. Let X and Y be positive "
                + "definite complex Hermitian matrices, let H be Hermitian with X+H and X-H "
                + "positive semidefinite, and let k be real with |k|<=1. Set S=Y^(-1/3), "
                + "A=SXS and B=SHS, using real continuous functional calculus for the matrix "
                + "power. For the actual function phi(t)=Re Tr[((Y+t kY)^(-1/3)(X+tH) "
                + "(Y+t kY)^(-1/3))^3], the positive-scalar CFC identity "
                + "(cY)^(-1/3)=c^(-1/3)S applies with c=1+kt>0 near zero. It yields "
                + "phi(t)=f(t) on a neighborhood of zero. The derivative formulas and "
                + "inequalities above therefore apply to phi, in particular phi''(0)>=0 "
                + "and |phi'''(0)|<=5phi''(0). Congruence by the Hermitian S preserves "
                + "both PSD endpoints; no pairwise commutation is used, and singular "
                + "endpoints are allowed. This application covers only alpha=3 and "
                + "radial second-variable directions.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-cubic-radial-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}

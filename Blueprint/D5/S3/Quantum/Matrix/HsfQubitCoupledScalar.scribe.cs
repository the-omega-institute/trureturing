using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfQubitCoupledScalarDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfQubitCoupledScalar";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete coupled scalar cubic bound for two positive spectral levels.",
        H("Coupled cubic estimate for two spectral levels"),
        Blocks(
            Entry("mean", "The cubic mean",
                "For real a and b define m(a,b)=2(a^2+ab+b^2)/(3(a+b)). "
                + "All estimates in this module assume the spectral levels are positive.",
                DescribeRole.Definition),
            Entry("excess", "Excess over the geometric mean",
                "The excess is e(a,b)=m(a,b)-sqrt(ab). It is homogeneous of degree one "
                + "under simultaneous positive scaling of a and b.", DescribeRole.Definition),
            Entry("penalty", "The off-diagonal penalty",
                "The cubic penalty is beta(a,b)=2(a-b)^2(a^2+3ab+b^2)/(9(a+b)). "
                + "It is homogeneous of degree three under simultaneous positive scaling.",
                DescribeRole.Definition),
            Entry("excess_nonneg", "The mean dominates the geometric mean",
                "For all real a>0 and b>0 the excess is nonnegative. "
                + "The proof uses 2sqrt(ab)<=a+b and the factorization "
                + "3(a+b)e=(a+b-2sqrt(ab))(2(a+b)+sqrt(ab)). "
                + "This auxiliary inequality is used by the complete coupled estimate.",
                DescribeRole.Theorem),
            Entry("coupled_cubic_le", "The full ordered, nonnegative-trace branch",
                "Let b>0 and a>=b. Let u lie in [-2a,2a], v in [-2b,2b], "
                + "u+v>=0, and x,w>=0. Suppose "
                + "w<=sqrt((2a-u)(2b-v))+e(a,b)x and x^2<=2(2a-u)/a. "
                + "Then (u+v)(u^2-uv+v^2+3w^2) is at most "
                + "2[a(u^2+w^2)+b(v^2+w^2)]+beta(a,b)x^2. "
                + "These hypotheses preserve the coupling supplied by the original PSD "
                + "endpoints; no maximizing phase, off-diagonal saturation, or quadratic "
                + "optimizer branch is assumed. The proof treats the zero margin, equal "
                + "levels, and zero row cases before any division. For small contrast it "
                + "uses a weighted variance identity and Young's inequality. For large "
                + "contrast it rescales to a=1,b=t^2 and directly consumes the exact "
                + "rectangle certificate in HsfQubitCubicCertificate.rectangular_J_nonneg. "
                + "Positive homogeneity restores arbitrary a and b.", DescribeRole.Theorem),
            Paragraph(Text("This is the scalar supplier for the complex Hermitian two by two "
                + "pure cubic coupling estimate associated with He-Saunderson-Fawzi "
                + "arXiv:2502.05627v1, Conjecture 6.2, and DOI 10.1007/s10107-025-02314-0, "
                + "Conjecture 1. The matrix endpoint-to-entry bridge, the simultaneous sign "
                + "and coordinate symmetry assembly, and the original sandwiched functional "
                + "are separate obligations. No arbitrary-dimensional or general-Y HSF "
                + "resolution, independent acceptance, or literature priority is asserted.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-qubit-coupled-scalar-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}

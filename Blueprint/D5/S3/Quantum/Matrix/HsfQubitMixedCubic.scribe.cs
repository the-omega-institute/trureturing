using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfQubitMixedCubicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfQubitMixedCubic";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original ordered trace coefficients and a positive six-row mixed cubic certificate.",
        H("Complex qubit mixed cubic compatibility"),
        Blocks(
            MatrixEntry("hermitian", "Hermitian coordinates",
                "The two by two matrix with real diagonal a,b and upper off-diagonal z; "
                + "the lower off-diagonal is the complex conjugate of z.", DescribeRole.Definition),
            MatrixEntry("hermitian_isHermitian", "Hermitian coordinate construction",
                "The coordinate matrix is Hermitian for every pair of real diagonal "
                + "entries and every complex off-diagonal entry.", DescribeRole.Theorem),
            MatrixEntry("hermitian_eq", "All Hermitian qubit matrices",
                "Every complex Hermitian two by two matrix equals the coordinate "
                + "matrix formed from its two real diagonal entries and its upper entry.",
                DescribeRole.Theorem),
            MatrixEntry("weightedImage", "A symmetric two point kernel",
                "For real a,b,m, weightedImage multiplies K00 by a, K11 by b, "
                + "and both off-diagonal entries by m.", DescribeRole.Definition),
            MatrixEntry("weightedImage_hermitian", "The kernel in Hermitian coordinates",
                "The kernel action sends the Hermitian coordinates r,s,z to "
                + "ar,bs,mz, for arbitrary real a,b,m.", DescribeRole.Theorem),
            MatrixEntry("endpoint_coupling", "The joint endpoint estimate",
                "For nonnegative a,b, let X-H with diagonal a-h,b-k and upper entry -z "
                + "and I+K with diagonal 1+r,1+s and upper entry w both be PSD. Then "
                + "|z|+sqrt(ab)|w| is at most sqrt((a-h+a(1+r))(b-k+b(1+s))). "
                + "The PSD determinant bounds and the two term Cauchy inequality "
                + "retain the original coupling; no inverse or strict endpoint is needed.",
                DescribeRole.Theorem),
            MatrixEntry("contraction_row", "The contraction row estimate",
                "For every complex Hermitian two by two K with both I+K and I-K PSD, "
                + "the squared modulus of K01 is at most 1-K00^2. Both determinant "
                + "constraints are used, and singular endpoints are allowed.", DescribeRole.Theorem),
            MatrixEntry("displacement_coupling", "The actual displacement entry",
                "If m>=sqrt(ab), the same coupled endpoints give "
                + "|z-mw|<=sqrt((2a-(h-ar))(2b-(k-bs)))+(m-sqrt(ab))|w|. "
                + "The argument uses the complex triangle inequality and the joint "
                + "endpoint estimate, with arbitrary complex phases.", DescribeRole.Theorem),
            MatrixEntry("displacement_row", "The weighted row estimate",
                "For a>0, h<=a and the two contraction endpoints of K, "
                + "|K01|^2<=2(2a-(h-aK00))/a. This also covers K01=0.",
                DescribeRole.Theorem),
            MatrixEntry("trace_weighted_square", "Exact weighted quadratic trace",
                "For the diagonal matrix X=diag(a,b) and Hermitian L with diagonal "
                + "u,v and upper entry z, Re Tr(XL^2)=a(u^2+|z|^2)+b(v^2+|z|^2). "
                + "All variables are arbitrary, and no positivity is assumed.",
                DescribeRole.Theorem),
            MatrixEntry("coupled_cubic_compatibility", "The complete qubit pure cubic estimate",
                "For every a,b>0 and complex Hermitian two by two H,K, assume "
                + "X+H,X-H,I+K,I-K are PSD, where X=diag(a,b). Put "
                + "m=2(a^2+ab+b^2)/(3(a+b)), M=weightedImage(a,b,m,K), "
                + "L=H-M and B=(a-b)^2(a^2+3ab+b^2)|K01|^2/(3(a+b)). "
                + "Then |Re Tr(L^3)|<=2 Re Tr(XL^2)+2B/3. There is no trace "
                + "restriction, no restriction on the complex off-diagonal phases, "
                + "and no assumption that an endpoint is invertible. The exact "
                + "coupled scalar estimate applies after a simultaneous sign reversal "
                + "and a coordinate exchange when required.", DescribeRole.Theorem),
            Entry("traceCoefficient2", "The original second trace coefficient",
                "For arbitrary square complex matrices indexed by a finite type, this is "
                + "the ordered trace-word polynomial p2 at alpha=3 and Y=I. It is defined "
                + "directly from the word table, independently of the positive certificate.",
                DescribeRole.Definition),
            Entry("traceCoefficient3", "The original third trace coefficient",
                "The third ordered trace-word polynomial p3 uses the original factor "
                + "orders. No commutation of X,H,K or inverse endpoint premise is added.",
                DescribeRole.Definition),
            Entry("coefficient2", "The real second coefficient",
                "The real part of traceCoefficient2. Its identification with one half "
                + "of the physical second derivative is a separate analytic obligation.",
                DescribeRole.Definition),
            Entry("coefficient3", "The real third coefficient",
                "The real part of traceCoefficient3. Its identification with one sixth "
                + "of the physical third derivative is a separate analytic obligation.",
                DescribeRole.Definition),
            Entry("trace_jet_coefficient2", "The second matrix trace jet",
                "In arbitrary finite dimension, set L=H-(2/3)XK and "
                + "M=-(4/3)HK+(10/9)XK^2. Then Tr(3MXX+6LLX)=2p2. "
                + "The exact identity uses trace cyclicity, with no Hermitian premise.",
                DescribeRole.Theorem),
            Entry("trace_jet_coefficient3", "The third matrix trace jet",
                "For the same L,M and N=(10/3)HK^2-(80/27)XK^3, "
                + "Tr(3NXX+9MLX+9MXL+6LLL)=6p3 in arbitrary finite dimension. "
                + "Every ordered word is retained until trace cyclicity is applied. "
                + "The actual function derivative supplier consumes this identity.",
                DescribeRole.Theorem),
            Entry("f", "The first row coefficient",
                "The real rational weight 2(a+2b)/(3(a+b)) in the first Gram row.",
                DescribeRole.Definition),
            Entry("q", "The cubic correction in the first row",
                "The real rational weight -(a-b)(3a^2+9ab+8b^2)/(18(a+b)^2).",
                DescribeRole.Definition),
            Entry("c", "The second Gram weight",
                "The weight (a-b)^2(2a+3b)/(a+b)^2, nonnegative at positive a,b.",
                DescribeRole.Definition),
            Entry("j", "The second row correction",
                "The real rational weight b^2/(3(a+b)) in the second Gram row.",
                DescribeRole.Definition),
            Entry("d", "The third Gram weight",
                "The weight (a-b)^2(a+2b)(7a^2+14ab+4b^2)/(36(a+b)^2).",
                DescribeRole.Definition),
            Entry("rowGram", "A complex row Gram matrix",
                "The two by two positive form R*R of rank at most one associated with R=(x,y).",
                DescribeRole.Definition),
            Entry("mixedMatrix", "Six weighted row-Gram forms",
                "For arbitrary real diagonal displacement entries and complex upper "
                + "entries w,z, mixedMatrix is a sum of six row-Gram matrices of rank at most one. "
                + "Its rational coefficients have denominators that are powers of a+b; "
                + "the definition therefore does not divide by the spectral gap a-b.",
                DescribeRole.Definition),
            Entry("mixedMatrix_posSemidef", "Positivity of the mixed certificate",
                "For every a,b>0 and arbitrary displacement entries, the six-row "
                + "certificate is positive semidefinite. No endpoint premise on H is needed.",
                DescribeRole.Theorem),
            Entry("coordinate_energy_identity", "The second coefficient energy identity",
                "Let X=diag(a,b), L have Hermitian coordinates u,v,w, K have coordinates "
                + "r,s,z, and H=L+weightedImage(a,b,m,K), where "
                + "m=2(a^2+ab+b^2)/(3(a+b)). If a+b is nonzero, then "
                + "p2=3 Re Tr(XL^2)+B, where "
                + "B=(a-b)^2(a^2+3ab+b^2)|z|^2/(3(a+b)). "
                + "The identity is derived by ordered matrix multiplication.",
                DescribeRole.Theorem),
            Entry("coordinate_mixed_cubic_bound", "The coordinate mixed bound",
                "For a,b>0 and I+K,I-K positive semidefinite, arbitrary complex Hermitian "
                + "L and H=L+weightedImage(a,b,m,K) satisfy "
                + "|3 Re Tr(L^3)-3p3|<=3p2. The exact identities "
                + "3 Tr(L^3)-3p3=Tr(KN) and Tr(N)=3p2, together with N>=0, "
                + "supply both signs of the bound.", DescribeRole.Theorem),
            Entry("mixed_cubic_bound", "The mixed bound for arbitrary Hermitian inputs",
                "For a,b>0 and arbitrary complex Hermitian two by two H,K, if I+K "
                + "and I-K are positive semidefinite, then with "
                + "L=H-weightedImage(a,b,m,K), |3 Re Tr(L^3)-3p3|<=3p2. "
                + "There is no endpoint restriction on H in this theorem.",
                DescribeRole.Theorem),
            Entry("energy_identity", "The energy identity without coordinates",
                "For arbitrary complex Hermitian H,K and a+b nonzero, the original "
                + "real coefficient p2 equals 3 Re Tr(XL^2)+B, with the same "
                + "weighted displacement and B as in the coordinate identity.",
                DescribeRole.Theorem),
            Entry("coefficient_compatibility", "Full qubit coefficient compatibility",
                "For a,b>0, X=diag(a,b), and arbitrary complex Hermitian two by two H,K, "
                + "assume X+H,X-H,I+K,I-K are positive semidefinite. Then p2>=0 and "
                + "3|p3|<=5p2. This combines the six-row mixed certificate with the "
                + "coupled pure cubic estimate. Spectral levels may coincide and "
                + "endpoints may be singular; complex phases are unrestricted.",
                DescribeRole.Theorem),
            Paragraph(Text("The source is a supplier for the alpha=3, Y=I, complex "
                + "two dimensional restriction of the He-Saunderson-Fawzi compatibility "
                + "question, arXiv:2502.05627v1 Conjecture 6.2 and published Conjecture 1, "
                + "DOI 10.1007/s10107-025-02314-0. Identification with derivatives of "
                + "the matrix power function is not asserted here. The unrestricted "
                + "HSF conjecture and literature priority remain unclaimed.")))));

    private static DocumentBlock MatrixEntry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-qubit-coupled-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-qubit-mixed-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}

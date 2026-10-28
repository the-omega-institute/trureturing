using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfQubitMixedCubicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfQubitMixedCubic";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original ordered trace coefficients and a positive six-row mixed cubic certificate.",
        H("Complex qubit mixed cubic compatibility"),
        Blocks(
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
            Entry("mixedMatrix", "Six weighted row-Gram forms",
                "For arbitrary real diagonal displacement entries and complex upper "
                + "entries w,z, mixedMatrix is a sum of six rank-one row-Gram matrices. "
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

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-qubit-mixed-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncompiled mathematical source candidate: complex PSD3 cubic geometry and exact scalar coefficients.",
        H("HsfThreeLevelCoefficients"),
        Blocks(
            Entry("H", "H",
                "The positive-level denominator p^2+pq+q^2.", DescribeRole.Definition),
            Entry("Q", "Q",
                "The product H(p,q)H(q,r)H(r,p).", DescribeRole.Definition),
            Entry("edgeNumerator", "edgeNumerator",
                "The actual pair numerator pq(p-q)^2(p^2-pq+q^2)(p^2+7pq+q^2).", DescribeRole.Definition),
            Entry("rho", "rho",
                "The canonical HsfBalancedSpectralCertificate.kappa evaluated at q/p; its explicit closed formula is proved for positive p,q.", DescribeRole.Definition),
            Entry("symmetricF", "symmetricF",
                "The explicitly specified degree-fifteen triangle numerator as a polynomial in the elementary symmetric variables.", DescribeRole.Definition),
            Entry("F", "F",
                "The triangle numerator at e=p+q+r, f=pq+qr+rp, g=pqr.", DescribeRole.Definition),
            Entry("Xi", "Xi",
                "The actual triangle coefficient 9pqrF/(4Q^3), equal to 6C_actual in the ordered normal form.", DescribeRole.Definition),
            Entry("closedCubic", "closedCubic",
                "The actual closed cubic with edge weights rho(p,q),rho(q,r),rho(r,p) and cycle coefficient Xi(p,q,r).", DescribeRole.Definition),
            Entry("H_pos", "H pos",
                "H(p,q) is strictly positive at positive levels.", DescribeRole.Theorem),
            Entry("Q_pos", "Q pos",
                "Every factor of Q is positive at positive levels, including collisions.", DescribeRole.Theorem),
            Entry("rho_closed", "rho closed",
                "The canonical kappa(q/p) equals the literal two-variable rho rational formula, without a spectral gap denominator.", DescribeRole.Theorem),
            Entry("rho_nonneg", "rho nonneg",
                "The actual pair coefficient is nonnegative at all positive levels.", DescribeRole.Theorem),
            Entry("rho_pos", "rho pos",
                "The actual pair coefficient is strictly positive when its two positive levels differ.", DescribeRole.Theorem),
            Entry("rho_symm", "rho symm",
                "The actual pair coefficient is symmetric in its two positive levels.", DescribeRole.Theorem),
            Entry("rho_self", "rho self",
                "The actual pair coefficient vanishes on a level collision.", DescribeRole.Theorem),
            Entry("F_nonneg", "F nonneg",
                "The actual triangle numerator is nonnegative for every positive triple. Its 118 positive ordered-chamber monomials and permutation symmetry establish the sign; this gives no sign to a complex source cycle.", DescribeRole.Theorem),
            Entry("Xi_nonneg", "Xi nonneg",
                "The actual scalar coefficient Xi is nonnegative at every positive triple, with all collisions retained.", DescribeRole.Theorem),
            Entry("Xi_double", "Xi double",
                "At a double collision Xi(p,p,q)=2rho(p,q). The factor two is preserved.", DescribeRole.Theorem),
            Entry("Xi_self", "Xi self",
                "At three equal levels Xi vanishes.", DescribeRole.Theorem),
            Entry("commonDen", "commonDen",
                "The common positive denominator 12Q^4 of the three pair weights and the cycle weight.", DescribeRole.Definition),
            Entry("edgeScaled", "edgeScaled",
                "The pair numerator multiplied by the fourth powers of the other two H factors.", DescribeRole.Definition),
            Entry("cycleScaled", "cycleScaled",
                "The literal scaled cycle numerator 27pqrQF.", DescribeRole.Definition),
            Entry("p396", "p396",
                "The cleared polynomial 4U1U2+396U3-U1H0^2, with Ui formed from the actual scaled pair numerators.", DescribeRole.Definition),
            Entry("edge_scaled", "edge scaled",
                "Exact binding of each scaled pair numerator to commonDen times the actual rho.", DescribeRole.Theorem),
            Entry("cycle_scaled", "cycle scaled",
                "Exact binding of the scaled cycle numerator to commonDen times the actual Xi.", DescribeRole.Theorem),
            Entry("p396_scaled", "p396 scaled",
                "The degree-seventy-two polynomial is exactly commonDen^3 times the actual coefficient comparison margin. This normalization alone does not assert its sign.", DescribeRole.Theorem),
            Paragraph(Text("These are source candidates, not compiled or frozen results. "
                + "The scalar P396 source was inspected as fallible mathematical input; "
                + "its separate independent audit was not read. No novelty is claimed. "
                + "The commutant equality classification, original integral-to-moment bridge "
                + "and original HSF derivative/source bridge remain unformalized here. "
                + "Required Lean, axiom, Scribe and registration checks have not run.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsfthreelevelcoefficients-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipChannelDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMDLipChannel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuation of the native lowered D-lip Laurent channel and A/D overlap",
        H("Fixed occupations and finite lowering"),
        Blocks(
            D("d-lip-charge-sector", "dLipChargeSector", "Fixed-occupation D-lip charge sector",
                DescribeRole.Definition,
                Text("For either lip, fix a mod-two class and four occupations. Sum over the charges "
                    + "in that class. Each term multiplies the inverses of (1−t)³ and the twelfth power "
                    + "of the continued D period by the D nome raised to the natural part of the "
                    + "charge energy and by the affine Gaussian coefficient for the fixed occupations. "
                    + "The matrix entries are successive Taylor coefficients at the external origins "
                    + "of the Gram-scaled signed covariance. The vector takes the corresponding mean "
                    + "coefficients with minus the leg sign, inverse period, and pairing of the "
                    + "label's unit charge with the summation charge.")),
            D("d-lip-charge-sector-analytic", "dLipChargeSector_analyticAt",
                "Analyticity of the D-lip charge sector", DescribeRole.Theorem,
                Text("For real positive definite Gram data, either lip, every mod-two class and "
                    + "all four occupations, the corresponding sector is complex analytic at "
                    + "each real t > 1."), Text(" Nonvanishing of the boundary period gives the "
                    + "analytic determinant factor. Apply "),
                Ref(FourPoint + "OriginalFourMSlitTaylor.analytic_coefficient_slice"),
                Text(" once to the joint mean and twice to the joint covariance. The tagged "
                    + "entries form a finite family, so they are analytic on a common ball where "
                    + "the determinant and nome are analytic and the nome has modulus less "
                    + "than one. On that ball apply "),
                Ref(FourPoint + "OriginalFourMSectorContinuation.charge_sector_differentiableOn"),
                Text(" and use complex differentiability on the ball.")),
            D("d-lip-channel", "dLipChannel", "Native lowered D-lip Laurent channel",
                DescribeRole.Definition,
                Text("For each mod-two class a, weight the lowered Laurent sum by the quadratic "
                    + "sign of a+b. The detector sums ell below the canonical lowering cutoff, "
                    + "with the canonical lowering weight at m+n+r. It uses input order P, R, Q "
                    + "and applies ell powers of the oscillator lowering operator to S. Each "
                    + "Laurent term has factor (−t) raised to −(H+L) and uses the shared occupation "
                    + "projection at weights H and L, Taylor degree zero, and Laurent index "
                    + "m+n+r+ell−H−L+1. "),
                Ref(FourPoint + "FourPointChannelCoefficients.loweringCutoff"), Text(", "),
                Ref(FourPoint + "FourPointChannelCoefficients.loweringWeight"), Text(", "),
                Ref(FourPoint + "OriginalFourMChargeNormal.projectOccupations"), Text(".")),
            D("d-lip-channel-analytic", "dLipChannel_analyticAt",
                "Analyticity of the lowered D-lip Laurent channel", DescribeRole.Theorem,
                Text("For any lattice data with positive definite real Gram matrix, either lip, "
                    + "all nonnegative weights H, K, L, integer modes m, n, r, oscillator inputs "
                    + "P, Q, R, S and mod-two output charge b, the channel is complex analytic at "
                    + "each real t > 1."), Text(" Unfold the shared occupation projection into its "
                    + "finite weighted sum of analytic sectors. The Laurent power is analytic "
                    + "because t is nonzero. Then take the finite lowering and charge-class sums "
                    + "with their coordinate-independent weights and quadratic signs.")),
            D("d-lip-charge-sector-eq-slit", "dLipChargeSector_eq_slit",
                "Agreement of fixed-occupation sector sums on the open D lip", DescribeRole.Theorem,
                Text("For either selected lip, each mod-two class and all four fixed occupations, "
                    + "the D-lip coset sum equals the canonical slit coset sum at every point of "
                    + "the open lip. The period and nome agree there. Transport the mean germ "
                    + "through its Taylor coefficient and the covariance germ through both "
                    + "successive coefficients. The resulting matrices, signed linear factors "
                    + "and energy weights agree term by term. "),
                Ref(FourPoint + "OriginalFourMSlitTaylor.coefficient_congr"), Text(", "),
                Ref(FourPoint + "OriginalFourMSectorContinuation.slitChargeSector")),
            D("d-lip-channel-eq-slit", "dLipChannel_eq_slit",
                "Agreement with the canonical D channel on the open lip", DescribeRole.Theorem,
                Text("For every lattice datum, the native D-lip channel and the canonical slit D "
                    + "channel agree at every point of the selected open lip. Apply sector agreement "
                    + "inside the shared occupation projection and use the same lowered Laurent "
                    + "detector and charge-class signs. "),
                Ref(Prefix + "dLipChargeSector_eq_slit"), Text(", "),
                Ref(FourPoint + "OriginalFourMSlitChartGerms.slitChannelD")),
            D("slit-ad-overlap", "slit_AD_overlap", "Conditional interior A/D chart overlap",
                DescribeRole.Theorem,
                Text("Assume a positive definite real Gram matrix and a real t greater than one. "
                    + "Explicitly assume that A at 1−s equals the continued D-lip channel at s "
                    + "throughout a real neighborhood of t. Complex analyticity on both sides of "
                    + "the equality gives agreement near t. Open-lip channel agreement gives equality "
                    + "with canonical D near an interior point u of that lip. Inversion gives "
                    + "y = u⁻¹ in U_A ∩ U_D and equality of A(1−z⁻¹) and D(z⁻¹) throughout "
                    + "a complex neighborhood of y. "),
                Ref(FourPoint + "OriginalFourMPeriodSource.eq_near_dLip_of_real_germ"), Text(", "),
                Ref(FourPoint + "OriginalFourMSlitChartGerms.slitChannelA_analyticOnNhd"), Text(", "),
                Ref(Prefix + "dLipChannel_analyticAt"), Text(", "), Ref(Prefix + "dLipChannel_eq_slit")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}

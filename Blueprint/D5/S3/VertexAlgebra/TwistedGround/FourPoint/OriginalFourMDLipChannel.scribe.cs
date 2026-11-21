using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipChannelDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMDLipChannel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analyticity of the native lowered D-lip Laurent channel",
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
                    + "with their coordinate-independent weights and quadratic signs.")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}

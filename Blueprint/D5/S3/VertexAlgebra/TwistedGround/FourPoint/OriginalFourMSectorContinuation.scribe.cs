using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSectorContinuationDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMSectorContinuation.";
    private const string SlitNome = "D5/S3/Analytic/OriginalSlitNome.";
    private const string SlitTaylor = FourPoint + "OriginalFourMSlitTaylor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal convergence and native agreement of the rank-24 charge-sector terms",
        H("Holomorphic fixed-occupation charge sectors on the Euler slit"),
        Blocks(
            D("charge-sector-holomorphy", "charge_sector_differentiableOn",
                "Holomorphy of a fixed-occupation coset sum", DescribeRole.Theorem,
                Text("Let the real Gram matrix be positive definite and fix four occupations and a "
                    + "mod-two charge class. On an open chart, assume the scalar prefactor, nome, "
                    + "covariance entries and signed mean factors are complex differentiable, with "
                    + "the nome strictly subunit. The actual coset sum is complex differentiable there. "
                    + "Around each point, a closed subball gives a summable majorant for the full "
                    + "charge family. Restriction to the chosen coset preserves that bound, and "
                    + "the finite occupation polynomial makes the individual terms holomorphic. "),
                Ref(FourPoint + "OriginalFourMChargeNormal.compact_charge_normal")),
            D("slit-charge-term", "slitChargeTerm", "Continued term at a fixed charge", DescribeRole.Definition,
                Text("In the square parameter r, multiply the rank-24 determinant by the specified "
                    + "occupation's affine coefficient and a power of the slit nome. The exponent is "
                    + "the integer charge energy converted to a natural number by Int.toNat. Negative "
                    + "charge energies give exponent zero. "
                    + "The two tagged copies of the finite support give its matrix and linear indices. "
                    + "The linear factor at each index is its slit mean entry times the charge pairing. "),
                Ref(SlitNome + "rank24Determinant"), Text(", "), Ref(SlitNome + "slitNome"), Text(", "),
                Ref(SlitTaylor + "slitCovarianceEntry"), Text(", "), Ref(SlitTaylor + "slitMeanEntry")),
            D("slit-charge-sector", "slitChargeSector", "Slit charge-sector sum", DescribeRole.Definition,
                Text("Sum the continued terms over charges in the selected mod-two class, "
                    + "with zero contribution from all other charges.")),
            D("slit-charge-sector-holomorphy", "slitChargeSector_differentiableOn",
                "Holomorphy throughout the Euler slit", DescribeRole.Theorem,
                Text("For each positive definite real Gram matrix and each fixed occupation and charge "
                    + "class, the slit sector sum is complex differentiable throughout the Euler slit. "
                    + "The determinant and the Taylor entries give the chart data, and the subunit "
                    + "nome gives a uniform strict bound on every compact subball. "),
                Ref(SlitNome + "slitNome_norm_lt_one"), Text(", "),
                Ref(SlitTaylor + "slitCovarianceEntry_analyticOnNhd"), Text(", "),
                Ref(SlitTaylor + "slitMeanEntry_analyticOnNhd")),
            D("slit-charge-term-native", "slitChargeTerm_eq_native", "Exact agreement with native sewing",
                DescribeRole.Theorem,
                Text("For a rank-24 lattice datum, any fixed occupations and any individual charge "
                    + "of nonnegative energy, the continued term at r = w² equals the original sewn term "
                    + "for every complex |w| < 1. The exact Taylor entries identify the native covariance "
                    + "and mean. The determinant uses the twelfth power of the Gaussian period identity, "
                    + "and the disk nome recovers the native displacement exponential, both charge scalars "
                    + "and the power of w. "),
                Ref(FourPoint + "OriginalFourMChargeNormal.sewnChargeTerm"), Text(", "),
                Ref("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity"),
                Text(", "), Ref(SlitNome + "slitNome_eq_Q0"), Text(", "),
                Ref(SlitTaylor + "slitCovarianceEntry_eq_native"), Text(", "),
                Ref(SlitTaylor + "slitMeanEntry_eq_native")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}

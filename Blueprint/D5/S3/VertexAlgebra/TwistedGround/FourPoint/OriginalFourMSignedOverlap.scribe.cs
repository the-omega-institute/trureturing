using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSignedOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.";

    private static DocumentBlock Result(string id, string declaration, string heading, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual signed external Gaussian on the native elliptic chart.",
        H("Signed Four-Point Covariance and Mean"),
        Blocks(
            Result("native-covariance-sum", "native_covariance_hasSum", "Native covariance series",
                "With the lattice Gram multiplier, the same-leg series is the signed J generator "
                + "plus the native free block. The crossed series is minus the signed T generator "
                + "in both leg orders. All sign pairs use the original complex radial domain."),
            Result("native-tagged-entry", "native_tagged_entry", "Native tagged matrix entry",
                "The two Taylor coefficients of this signed spatial generator recover the "
                + "effective matrix entry at arbitrary original external labels, including repeated labels."),
            Result("native-mean", "native_mean", "Native mean in each mode",
                "The actual charge pairing multiplies the signed source amplitude divided by the "
                + "period. The left mean has a minus sign and the right mean has a plus sign."),
            Result("native-mean-sum", "native_mean_hasSum", "Native mean series",
                "Summing over modes yields the signed half-coordinate source times the negative "
                + "charge pairing divided by the slit period."),
            Result("native-spatial-overlap", "native_spatial_overlap", "Elliptic spatial kernels",
                "The same-leg mixed free block restores the Cauchy term. The equal-orientation "
                + "same-leg block retains the Cauchy subtraction. The crossed block uses the "
                + "second elliptic point on the other leg and the native minus sign."),
            Result("native-diagonal", "native_diagonal", "Regular same-orientation diagonal",
                "The removable diagonal of the Cauchy-subtracted block is the limiting "
                + "signed J formula with the actual slit-period correction."),
            Result("half-coordinate-pullback", "half_coordinate_pullback", "Half-coordinate differential",
                "At the squared native coordinate, the signed source is the coefficient of "
                + "the pullback of dx/(2y). The right-leg lift reverses the differential."),
            Result("native-geometric-covariance", "native_geometric_covariance", "Geometric covariance",
                "Restoring only the same-puncture subtraction gives the elliptic kernel multiplied by "
                + "the two signed half-coordinate differentials."),
            Result("native-a-covariance-discrepancy", "native_A_covariance_discrepancy", "A to B and D covariance differences",
                "The A source on the native convergence overlap gives the period-product differences "
                + "from the B and D spatial kernels in the pulled-back differential units."),
            Result("chart-source-at-puncture", "chart_source_at_puncture", "Source at the physical puncture",
                "The signed source at zero divided by the chosen root of the physical scale gives "
                + "the chart's half-differential at the corresponding puncture."),
            Result("chart-chosen-source-signs", "chart_chosen_source_signs", "Relative puncture signs",
                "In the common physical puncture order, the A to B signs are positive except at S "
                + "and the A to D signs are negative at Q and R."),
            Result("chosen-chart-source-native", "chosen_chart_source_eq_native", "Native source germ on A and B",
                "The selected normalized root agrees with the literal signed source germ wherever "
                + "the A or B period parameter belongs to the native disk."),
            Result("chosen-chart-source-analytic", "chosen_chart_source_analytic", "Source at all three puncture charts",
                "The normalized square root defines an analytic germ at the origin of each spatial coordinate."),
            Result("chart-covariance-native", "chart_covariance_eq_native", "Native covariance germ on A and B",
                "The chart kernels agree with the native J-plus-free and minus-T series on their initial "
                + "A and B convergence overlaps, including both mode origins."),
            Result("chart-covariance-analytic", "chart_covariance_analytic", "Regular chart covariance",
                "With the chosen source roots and actual period corrections, every signed covariance is "
                + "jointly analytic at the pair of mode origins in A, B and D."),
            Result("chart-d-source-boundary", "chartD_source_boundary", "Signed source on the D lip",
                "The selected source is the one-sided limit of the normalized slit source from the "
                + "matched D half-plane, with the actual root and its sign."),
            Result("chart-d-covariance-boundary", "chartD_covariance_boundary", "Signed covariance on the D lip",
                "The signed covariance has the corresponding one-sided limit using the actual D "
                + "period and derivative. The branch and denominator conditions specify its spatial domain."),
            Result("chart-spatial-overlap", "chart_spatial_overlap", "Elliptic covariance on all three charts",
                "The continued signed kernels use the actual elliptic rational kernel and period correction "
                + "on their punctured domains. The mixed same-leg term includes the native free contraction."),
            Result("chart-same-slot-covariance", "chart_same_slot_covariance", "Physical normal-ordering correction",
                "The physical Cauchy subtraction differs from the native equal-orientation subtraction "
                + "by the regular correction for the chosen scale at the actual puncture."),
            Result("chart-same-slot-origin", "chart_same_slot_origin", "Finite covariance at a coincident puncture",
                "The same-slot covariance tends to the regular value at the native mode origins in "
                + "each chart, with the selected period correction and orientation."),
            Result("slit-covariance-native", "slit_covariance_eq_native", "Original germ of the slit covariance",
                "The slit expression used in the D boundary theorem agrees with the original "
                + "signed mode generator near both mode origins throughout the native radial disk."))));
}

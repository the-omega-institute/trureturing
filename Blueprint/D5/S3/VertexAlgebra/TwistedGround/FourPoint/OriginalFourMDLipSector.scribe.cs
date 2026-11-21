using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipSectorDocument : IScribeDocumentDefinition
{
    private const string FourPoint = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/";
    private const string Prefix = FourPoint + "OriginalFourMDLipSector.";
    private const string LipNome = FourPoint + "OriginalFourMDLipNome.";
    private const string LipTaylor = FourPoint + "OriginalFourMDLipTaylor.";
    private const string SlitSector = FourPoint + "OriginalFourMSectorContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic continuation of the original fixed-occupation D-lip charge-sector sum",
        H("Analyticity at the D boundary and equality with the slit sector"),
        Blocks(
            D("d-lip-charge-sector", "dLipChargeSector", "Fixed-occupation charge-sector sum on the D lip",
                DescribeRole.Definition,
                Text("For the selected lip and charge class, form the affine coefficient from the signed "
                    + "D-lip Taylor entries and charge pairings. Each term carries the D nome to the "
                    + "natural charge energy and the factor (1 − r)⁻³ times the D period to power −12. "
                    + "The sum keeps precisely the selected mod-two charge class. "),
                Ref(LipNome + "dNome"), Text(", "),
                Ref(LipTaylor + "dLipMeanEntry"), Text(", "), Ref(LipTaylor + "dLipCovarianceEntry")),
            D("d-lip-charge-sector-analytic", "dLipChargeSector_analyticAt",
                "Analytic continuation at every real t > 1", DescribeRole.Theorem,
                Text("For a positive definite real Gram matrix, either lip and every fixed occupation "
                    + "and charge class, the charge-sector sum is analytic at t viewed in ℂ. "
                    + "Finiteness of the tagged support gives a common neighborhood where all mean "
                    + "and covariance entries are holomorphic. The determinant is holomorphic there "
                    + "after restricting the neighborhood, and the D nome stays strictly subunit. "
                    + "Apply the open-chart coset convergence theorem on a ball in that neighborhood. "),
                Ref(LipNome + "dNome_subunit_near"), Text(", "),
                Ref(SlitSector + "charge_sector_differentiableOn")),
            D("d-lip-charge-sector-slit", "dLipChargeSector_eq_slit",
                "Termwise agreement on the selected open D lip", DescribeRole.Theorem,
                Text("At every point of the chosen open lip, the two sector sums agree for all "
                    + "occupations and charge classes. The point lies on the double slit, so equality "
                    + "of the period-ratio exponentials gives nome agreement. The D period and both "
                    + "Taylor entries also take their slit values, giving equality at every charge. "),
                Ref(LipNome + "dNome_eq_exp"), Text(", "),
                Ref("D5/S3/Analytic/OriginalSlitNome.slitNome_eq_exp"), Text(", "),
                Ref(FourPoint + "OriginalFourMPeriodSource.dPeriod_eq_slit"), Text(", "),
                Ref(LipTaylor + "dLipMeanEntry_eq_slit"), Text(", "),
                Ref(LipTaylor + "dLipCovarianceEntry_eq_slit")))));

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}

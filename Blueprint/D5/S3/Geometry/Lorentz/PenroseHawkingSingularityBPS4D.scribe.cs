using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class PenroseHawkingSingularityBPS4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/PenroseHawkingSingularityBPS4D.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Observer/bousso2002lightsheetfocusing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-dimensional focusing and extremal potentials.",
        H("Four-dimensional focusing and extremal potentials"),
        Blocks(
            Paragraph(Text("The focusing statements concern regular affine intervals or positive FLRW scale factors. With zero shear and Ricci terms, the initial tangent can reach zero exactly at the null focusing ceiling. The potential calculation uses Cartesian derivatives away from all centers.")),
            Entry("penrose-trapped-surface-caustic-bound", "penrose_trapped_surface_caustic_bound", "Null focusing from a trapped initial value",
                "On a closed forward affine interval, the null Raychaudhuri equation, nonnegative shear square and nonnegative null Ricci term imply strict decrease and negativity from negative initial expansion. The reciprocal is bounded below by its initial value plus half the elapsed affine parameter. The length of the regular interval is strictly less than two divided by the absolute initial expansion."),
            Entry("penrose-shear-strictly-accelerates-focusing", "penrose_shear_strictly_accelerates_focusing", "Strict focusing with initial shear or Ricci curvature",
                "For the same differential equation and nonnegative focusing terms, a strictly positive initial shear square or Ricci term makes the reciprocal comparison strict at every positive affine parameter in the regular interval. The proof uses the positive right derivative of the reciprocal surplus at the initial point."),
            Entry("bousso-lightsheet-area-monotonicity", "bousso_lightsheet_area_monotonicity", "Concave optical radius and light-sheet area",
                "For a positive Sachs radius under null convergence and nonpositive initial expansion, the square root of the area is concave, expansion stays nonpositive and the area is antitone. When the initial expansion is negative the radius is bounded above by its initial tangent and the positive-radius interval has length strictly below the null focusing ceiling."),
            Entry("hawking-past-big-bang-bound", "hawking_past_big_bang_bound", "Past lifetime of a positive FLRW scale factor",
                "On a past interval of positive duration, if the scale factor is differentiable with antitone derivative, and the final scale factor and its derivative are positive, the final Hubble rate is positive. The final tangent bounds the scale factor above throughout the interval. Positivity throughout the interval forces its length strictly below the reciprocal Hubble rate."),
            Entry("hawking-timelike-congruence-raychaudhuri", "hawking_timelike_congruence_raychaudhuri", "Timelike Raychaudhuri ceiling",
                "A differentiable timelike expansion with negative initial value and derivative bounded above by minus one third of its square has a regular interval of length strictly less than three divided by the absolute initial expansion."),
            Entry("bps-extremal-force-cancellation", "bps_extremal_force_cancellation", "Same-sign extremal force cancellation",
                "For positive separation and positive masses, if both charges equal their masses or both equal the negatives of their masses, the signed radial force vanishes and the gravitational and Coulomb magnitudes are equal and positive. Both nonrotating surface gravities vanish."),
            Entry("bps-superposition-charge-bound", "bps_superposition_charge_bound", "Extremal mass and charge sums",
                "For a finite family with charge equal to mass at each center, the sums of the mass and charge parameters are equal."),
            Entry("bps-subextremal-attraction", "bps_subextremal_attraction", "Strict subextremal attraction",
                "For positive separation and positive second mass, strict subextremality of the first charge and weak subextremality of the second charge force the signed radial force to be negative."),
            Entry("inv-r3-harmonic-3d", "inv_r3_harmonic_3d", "First and second partial derivatives of inverse distance",
                "Away from the center, in each of the three coordinate directions the first derivative is minus the coordinate displacement divided by the cubed radius. The second derivative is three times its squared displacement divided by the fifth power of the radius, minus the inverse cubed radius. The sum of the three second derivatives vanishes."),
            Entry("majumdar-papapetrou-harmonic", "majumdar_papapetrou_harmonic", "Harmonic multicenter potential",
                "For any finite family of real masses and centers, the potential is harmonic at each point different from every center. If the masses are nonnegative and one is positive, the potential exceeds one there. The potential tends to one along each unit ray at positive infinity."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}

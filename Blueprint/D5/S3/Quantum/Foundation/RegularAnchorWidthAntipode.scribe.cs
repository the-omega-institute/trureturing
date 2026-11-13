using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RegularAnchorWidthAntipodeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual ratio image is convex, and the entire original effect interval detects antipodal contact and unit support at a regular anchor.",
        H("Convex actual ratios, full original width and antipodal contact"), Blocks(
        Paragraph(Text("Keep the original finite dimensional real carrier V, closed generating cone C, strictly positive unit u, complete base K and full effect interval 0 <= f <= u. Every original exclusion has a full three-ball chart, and equality of exclusions identifies their pure labels. At the original regular anchor p the actual common confirmer e is unique. The NativeChart input is derived by RegularAnchorNormalChart.regular_anchor_native from precisely these original hypotheses; it supplies neither a free positivity bridge nor a chosen subfamily of effects.")),
        Describe.Lean(DescribeId.Create("actual-image"), DeclarationHandle.Create(Owner + "actualImage"),
            H("Entire actual ratio image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Z is the image of every x in K other than p under H(x)/g(x), where g=u-e. NativeChart proves g is positive on this entire domain. No closedness of the pure state carrier is assumed."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("convex-image"), DeclarationHandle.Create(Owner + "actual_image_convex"),
            H("Convexity of the entire actual image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For two original states x,y and nonnegative weights s,t summing to one, normalize s*x/g(x)+t*y/g(y) by d=s/g(x)+t/g(y). Both gaps are strictly positive, hence d is positive. The resulting original base state has gap 1/d and its actual ratio is the requested convex combination. It cannot be the anchor. Closure preserves convexity; the existing whole-image norm bound makes S compact. The entire actual unit ball lies in S, giving nonempty ambient interior."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("rho"), DeclarationHandle.Create(Owner + "rho"),
            H("Actual directional support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("rho(v) is the supremum of -inner(v,z) over the whole actual ratio image. It is the exact source supremum of -inner(v,H(x))/g(x) over all x in K other than p."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actual-bound"), DeclarationHandle.Create(Owner + "actual_image_bound"),
            H("Whole actual image is bounded"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There is a finite positive M bounding the norm of every actual ratio image. Divide the proved whole-cone NativeChart bound by the strictly positive gap on K except p."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("inner-ball"), DeclarationHandle.Create(Owner + "ball_subset_actual"),
            H("The whole inner ball is actual"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every vector w in the closed unit ball is the ratio image of the actual state a(w), with gap exactly one. This state cannot equal p, whose gap is zero."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("support-bounded"), DeclarationHandle.Create(Owner + "rho_values_bdd"),
            H("Every full support supremum is bounded"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every vector v the entire set of support readings on Z is bounded above by norm(v)*M. The real supremum therefore has its ordinary upper-bound meaning."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("rho-upper"), DeclarationHandle.Create(Owner + "rho_le_iff"),
            H("Whole-base support bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real r and every coordinate vector v, rho(v)<=r is equivalent to -inner(v,H(x))<=r*g(x) for every original base state x other than p. The whole-cone NativeChart bound proves that the defining supremum is finite."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("rho-lower"), DeclarationHandle.Create(Owner + "rho_unit_lower"),
            H("Actual inner-ball lower bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every unit v, rho(v)>=1 because the actual original chart point a(-v) has g=1 and H=-v. This uses an actual state in the original exclusion."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("direction"), DeclarationHandle.Create(Owner + "direction"),
            H("Original directional linear effect"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The real linear functional direction(v) on V is inner(v,H). Its coordinate expansion lies in the entire signed normal span. The proved restriction isomorphism, rather than an additional premise, reconstructs every normalized positive annihilator with slope v as g+direction(v)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("antipodal"), DeclarationHandle.Create(Owner + "rho_one_iff_antipodal"),
            H("Exact actual antipodal criterion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every unit v, rho(v)=1 exactly when some effect in the entire original interval takes one at a(v) and zero at a(-v). Positivity is derived on the full original cone from the ratio bound; ExclusionWidthCompactness.comparison_zero_iff identifies actual comparison zero with exclusion in both directions, so an arbitrary original separating effect enters the existing comparison and slope-body theorem. The source direction v and the actual chart antipodes are retained without reversing or replacing their carriers."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("oscillation"), DeclarationHandle.Create(Owner + "oscillation"),
            H("Entire exclusion oscillation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Oscillation is the supremum of f on the entire original exclusion minus its infimum there. This is ExclusionWidthCompactness.oscillation on the same entire exclusion. Every original real linear effect is continuous in the finite dimensional topology."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("width"), DeclarationHandle.Create(Owner + "width"),
            H("Full original effect width"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("W(D(p)) is the ExclusionWidthCompactness.width of the entire exclusion: the supremum of its oscillation over all effects in the full original interval 0<=f<=u. The attainment theorem proves this is the source maximum, so the supremum notation does not weaken the source definition or remove an effect."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("width-attained"), DeclarationHandle.Create(Owner + "width_attained"),
            H("Actual full-effect width attainment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There exist a real linear effect f on the original carrier and a unit coordinate vector v such that W(D(p))=f(a(v))-f(a(-v)). The same actual f maximizes at a(v) and minimizes at a(-v) over the whole exclusion. ExclusionWidthCompactness.width_attained supplies a maximizing effect and actual extrema on the compact entire exclusion. For that same effect, the affine slope formula supplies one unit direction with antipodal extrema, including the constant-slope case."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("width-one"), DeclarationHandle.Create(Owner + "width_one_iff_rho_one"),
            H("Exact width and actual unit-support equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Width equals one if and only if an actual unit direction v satisfies rho(v)=1. If width is one, its attaining effect has actual readings one and zero at its antipodal extrema. Conversely any effect supplied by the unit-support criterion gives a full-exclusion oscillation of at least one, while ExclusionWidthCompactness.original_exclusion_width bounds the whole width by one. The reverse inequality applies ExclusionWidthCompactness.effect_difference_le_width to the same actual separating effect and chart antipodes. All quantifiers range over the original cone, base, effect interval and actual full chart."))), DescribeRole.Theorem),
        Paragraph(Text("RegularAnchorShell proves the attained entire-sphere minimum, actual shell-contact criterion, scaled-ball containment and positive boundary distance. RegularAnchorContactCriterion.regular_anchor_contact_criterion derives this same normal chart from the original hypotheses and combines these results into the complete Theorem 122.13. The scope remains the declared original mathematical cone and effect system; no physical realization or literature novelty is asserted."))
        )));
}

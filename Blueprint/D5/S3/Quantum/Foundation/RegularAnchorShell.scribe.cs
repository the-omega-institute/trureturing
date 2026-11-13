using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RegularAnchorShellDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/RegularAnchorShell.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The closure of the actual regular-anchor ratio image has exact support, an attained sphere minimum and inner-ball contact.",
        H("Actual regular-anchor shell"), Blocks(
        Paragraph(Text("Keep the same finite dimensional real carrier V, original cone C, unit u, entire base K, pure anchor p, actual common effect e and full three-ball chart a. NativeChart is the derived interface of RegularAnchorNormalChart.regular_anchor_native, obtained from the original closedness, strict positivity, generation, EB3, exclusion injectivity and regularity hypotheses. Every result below applies to that very interface. The ratio image and rho are those of RegularAnchorWidthAntipode; neither is replaced by a model or a restricted state family.")),
        Describe.Lean(DescribeId.Create("shell"), DeclarationHandle.Create(Owner + "shell"),
            H("Closed actual shell"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("S is the closure of the image of every state x in K other than p under H(x)/g(x), with g=u-e. The actual image need not be closed."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("convex-image"), DeclarationHandle.Create(Owner + "actual_image_convex"),
            H("Convexity of the entire actual image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For two original states x,y and nonnegative weights s,t summing to one, normalize s*x/g(x)+t*y/g(y) by d=s/g(x)+t/g(y). Both gaps are strictly positive, hence d is positive. The resulting original base state has gap 1/d and its actual ratio is the requested convex combination. It cannot be the anchor. Closure preserves convexity; the existing whole-image norm bound makes S compact. The entire actual unit ball lies in S, giving nonempty ambient interior."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("support"), DeclarationHandle.Create(Owner + "shell_support_le_iff"),
            H("Exact shell support relation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real bound r and every vector v, all z in S satisfy -inner(v,z)<=r exactly when rho(v)<=r. Continuous linear evaluation extends the upper bound from the entire actual image to its closure. Thus the ordinary support of S at -v is precisely the original rho(v)."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lipschitz"), DeclarationHandle.Create(Owner + "rho_lipschitz"),
            H("Global directional Lipschitz bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A finite positive M bounds every ratio vector. Cauchy-Schwarz bounds each change of support reading by M times norm(v-w). Taking the bounded real supremum in both directions gives the absolute difference estimate for all vectors v,w, and therefore continuity on the whole coordinate space."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("minimum"), DeclarationHandle.Create(Owner + "minimum"),
            H("Entire sphere minimum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The real infimum is taken over rho evaluated on the entire unit sphere of the actual three-dimensional coordinate space."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("attainment"), DeclarationHandle.Create(Owner + "minimum_attained"),
            H("Attainment and inner-ball lower bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Continuity on the nonempty compact sphere supplies an actual unit minimizing direction. Its value equals the defined infimum and is at least one; every other unit direction has value at least this same minimum. The infimum is therefore the source minimum, with no assumed attainment field."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("contact-direction"), DeclarationHandle.Create(Owner + "ball_frontier_direction"),
            H("Actual contact point identifies the direction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If z lies both in the closed inner ball and on the boundary of S, then norm(z)=1 and rho(-z)=1. A supporting functional exists because S is convex with nonempty interior. Riesz representation and normalization give its unit normal b. Inner-ball containment yields 1<=inner(b,z)<=norm(z)<=1; equality forces b=z. The direction in rho is exactly -z."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("unit-support-contact"), DeclarationHandle.Create(Owner + "rho_one_frontier"),
            H("Unit support gives the actual point -v"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For unit v with rho(v)=1, the actual image already contains -v, supplied by the original chart state a(-v). This point belongs to S and saturates its supporting inequality. Any interior neighborhood would contain a slightly farther point in direction -v, contradicting that inequality. Hence -v belongs to the shell boundary."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("minimum-contact"), DeclarationHandle.Create(Owner + "minimum_one_iff_contact"),
            H("Exact sphere-minimum and ball-boundary equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The minimum equals one exactly when the closed original coordinate unit ball meets the boundary of its actual shell. An attaining unit direction supplies the contact point -v. Conversely an actual contact z supplies the unit direction -z with rho(-z)=1, while the minimum is at least one. No smoothness, strict convexity or closedness of the actual ratio image is assumed."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("halfspaces"), DeclarationHandle.Create(Owner + "mem_shell_iff"),
            H("All unit support halfspaces reconstruct the actual shell"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A vector z belongs to S exactly when -inner(v,z)<=rho(v) for every unit v. For a point outside the actual closed convex S, strict separation supplies a real continuous functional. Its nonzero Riesz vector gives a unit direction contradicting the asserted inequality. This reconstruction is proved for the actual shell rather than supplied as a bridge premise."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("minimum-ball"), DeclarationHandle.Create(Owner + "minimum_ball_subset"),
            H("Containment at the minimum support radius"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The entire closed ball of radius delta=minimum(rho) lies in S. For every unit support direction, Cauchy-Schwarz bounds the reading of a vector in this ball by delta, which is no greater than its actual directional support. The proved halfspace reconstruction gives containment. Since delta>=1, this closed ball is exactly delta times the closed unit ball."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("strict-margin"), DeclarationHandle.Create(Owner + "strict_margin"),
            H("Strict containment and every boundary distance"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If delta>1, the entire original closed unit ball lies in the ambient interior of S. Every boundary point has norm at least delta, since the open ball of radius delta lies in the shell interior. The triangle inequality then gives dist(x,y)>=delta-1 for every inner-ball x and every boundary y."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("boundary-distance"), DeclarationHandle.Create(Owner + "boundaryDistance"),
            H("Distance of the whole ball from the whole boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The set distance is the real infimum of all distances dist(x,y), with x in the entire closed unit ball and y on the entire boundary of S. Both sets are nonempty: S contains the unit ball and is a bounded proper convex body, so its boundary is nonempty."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("positive-distance"), DeclarationHandle.Create(Owner + "strict_boundary_distance"),
            H("Positive distance from the actual boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For delta>1, the set distance is at least delta-1, and delta-1 is strictly positive. Nonemptiness of the distance-value set gives the ordinary real-infimum lower bound; the estimate covers every pair of actual points in the specified sets."))), DescribeRole.Theorem),
        Paragraph(Text("RegularAnchorContactCriterion.regular_anchor_contact_criterion derives the normal chart from the original cone, unit, full EB3, exclusion injectivity and regular-anchor hypotheses. It combines width_one_iff_rho_one with the attained full-sphere minimum and the actual contact equivalence, and proves the entire strict-scale conclusion for that same derived chart. These results preserve the actual chart signs and complete original state and effect domains. They do not assert a physical realization or literature novelty."))
        )));
}

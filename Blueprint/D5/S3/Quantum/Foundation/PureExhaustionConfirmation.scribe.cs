using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class PureExhaustionConfirmationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure-point exhaustion restores the original mixed comparison and complementary least effects.",
        H("Pure exhaustion on the full original carrier"),
        Blocks(
            Paragraph(Text("The carrier is a nonzero finite-dimensional real normed space with a closed pointed generating cone C and a unit u strictly positive on nonzero cone points. The normalized base is the entire original base C intersected with u=1, and pure points are every extreme point of that base. Effects are the complete original interval of linear maps f with 0<=f<=u on the whole cone. No finiteness, closedness, or exposedness assumption is made on the pure-point set.")),
            Paragraph(Text("The continuous-linear-map presentation proves compactness of the complete proper-effect interval: closedness is the intersection of the pointwise cone inequalities, while pure spanning and a finite basis give a uniform operator-norm bound. Each confirming face is a nonempty closed slice of that compact set. Consequently every original comparison infimum is attained, including a zero value at an opposing pure point.")),
            Paragraph(Text("For fixed pure p and q, assume only the pure relation T_p(r)+T_q(r)=1 for every original extreme point r. Every pair of confirming effects then gives a closed halfspace containing all pure points. Krein–Milman closure extends these inequalities to the entire original base; an attained confirmer for q that vanishes at p supplies the opposite upper bound. Thus the relation holds on every mixed original state and restricts back to the pure relation.")),
            Paragraph(Text("The lower envelopes are affine on every finite pure convex combination because each is concave and their sum is constant. Signed finite relations are normalized by positive and negative parts, with the zero vector and zero coefficients retained; the existing full-pure circuit descent then supplies linear effects e_p and e_q. Pure bounds extend to the whole cone, so each effect is proper, confirms its reference, and is least against every original confirmer. They agree with the attained comparison on the entire cone, and pure spanning gives e_p+e_q=u. The same argument forces p!=q and produces an attained confirmer for q whose value at p is zero.")),
            Describe.Lean(
                DescribeId.Create("proper-compact"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/PureExhaustionConfirmation.proper_compact"),
                H("Compactness of the complete original proper-effect interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full proper-effect set on continuous linear maps is compact under the original closed cone, strictly positive unit, and generating-span hypotheses. The proof uses all original pure points only to obtain a finite-dimensional norm bound; it does not replace them with a finite carrier."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("face-compact"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/PureExhaustionConfirmation.face_compact"),
                H("Every confirming face is compact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original pure point p, the complete confirming face is a compact nonempty closed slice of the original effect interval."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("comparison-attained"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/PureExhaustionConfirmation.comparison_attained"),
                H("Original comparison infima are attained"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every original cone point x, the infimum defining comparison for a pure reference p is reached by an original linear confirmer. The proof transports a compact continuous face minimizer back to the existing linear-map comparison."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-pair-relation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/PureExhaustionConfirmation.purePairRelation"),
                H("Pure-only complementary comparison relation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed original pure p and q, purePairRelation is the exact premise T_p(r)+T_q(r)=1 for every extreme point r of the entire original base."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pure-exhaustion-entry"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/PureExhaustionConfirmation.pure_exhaustion_entry"),
                H("Pure exhaustion yields mixed equality and complementary least effects"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under purePairRelation, p and q are distinct; an attained confirmer for q vanishes at p; the comparison sum is one on every mixed point of the original base; and linear effects e_p,e_q are proper, confirm their references, least on the whole cone, equal the attained comparisons on the whole cone, and satisfy e_p+e_q=u. This entry does not claim the later ball, compact-closure/Haar, same-H control-group, 98.4, or 98.5 resource conclusions."))), DescribeRole.Theorem))));
}

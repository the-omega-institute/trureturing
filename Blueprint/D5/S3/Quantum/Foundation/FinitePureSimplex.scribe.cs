using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FinitePureSimplexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-relation zero gluing on the entire original base.",
        H("One-relation zero gluing on the entire original base"),
        Blocks(
            Paragraph(Text("Finiteness applies to the full set of extreme points of the original normalized base. The carrier, cone, unit, full proper interval and original infimum comparison are unchanged. The one-relation equivalence imposes no ball, antipodal, Jordan or matrix premise.")),
            Describe.Lean(DescribeId.Create("simplex"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureSimplex.simplex"),
                H("The entire base as a simplex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The family of all original pure vertices is affinely independent over the real scalars and the entire base equals their convex hull."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zero-kernel-least-confirmation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureSimplex.zero_kernel_least_confirmation"),
                H("Whole-cone least coordinate confirmation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("If the full pure coordinate kernel is zero, there exists an original effect e_p for every original pure p. Each is proper and confirms p, has value one at p and zero at the other pure vertices, is dominated on every vector of the entire cone by every original proper confirmer of p, and attains T_p at every cone vector. For any two actual mixed-state exclusions, least domination forces both coordinate readings to vanish, so the same coordinate effect excludes their midpoint. No claim that an arbitrary mixed x different from p has zero p-coordinate is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-gluing-iff-simplex"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureSimplex.zero_gluing_iff_simplex"),
                H("The full finite one-relation theorem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("If the real dimension of the entire kernel of Phi is at most one, then original mixed-state zero gluing is equivalent to the entire base being a simplex. The zero-nullity branch constructs least coordinate effects against all confirmers. In the nonzero one-dimensional branch, a globally minimal nonzero relation coefficient is oriented positively. Extremality excludes a relation with a single vertex on either sign side. Full-kernel-annihilating original effects exclude each negative vertex separately. Original midpoint gluing supplies a common effect at a midpoint; nonnegativity makes that effect vanish at both endpoints, hence at every convex combination. This gives convexity of the actual exclusion set without assuming general infimum attainment. The same relation forces a positive lower bound at the source barycenter, contradicting any excluding effect. The normalized weighted theorem supplies the sharper attained partition values on the same original objects."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("whole-pair-base"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureSimplex.wholePairBase"),
                H("The entire smallest two-ray face"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For original p,q, this is the entire original normalized base intersected with every native cone face containing p and q. The universal intersection defines the whole smallest cone face, without replacing it by an arbitrary selected subface."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("antipodal-separation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureSimplex.antipodalSeparation"),
                H("Global effects for intrinsic pure antipodes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every distinct original pure pair p,q, every pure a on their entire smallest face, every center c whose reflection preserves that entire face, and every original pure r=2c-a, an original proper confirmer of a vanishes at r. For an entire ball its intrinsic center and antipodes are among these quantified objects; thus this formulation supplies the source antipodal condition on every original ball. It makes no assumption that a restricted face effect extends globally."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("antipodal-failure-nullity-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePureSimplex.antipodal_failure_nullity_bound"),
                H("At least two full preparation relations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the same finite full pure carrier, original mixed-state midpoint gluing together with a failure of the quantified intrinsic pure-antipode separation implies both dim ker Phi >= 2 and |P|-dim A >= 2. Under nullity at most one the main theorem gives a simplex and coordinate effects distinguish every distinct pure pair. A pure fixed point of reflection about a symmetry center of an entire face containing two distinct pure points is impossible: extremality at that midpoint would force both points to equal it. Rank-nullity and the derived surjectivity give dim A + dim ker Phi=|P|. In the source ball domain this is the consequence (92.7); no ball premise is needed by this stronger finite-carrier obstruction."))), DescribeRole.Theorem))));
}

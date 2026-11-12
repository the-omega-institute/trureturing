using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FinitePureSimplexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-relation zero gluing on the entire original base.",
        H("One-relation zero gluing on the entire original base"),
        Blocks(
            Paragraph(Text("Finiteness applies to the full set of extreme points of the original normalized base. The carrier, cone, unit, full proper interval and original infimum comparison are unchanged. No ball, antipodal, Jordan or matrix condition is imposed.")),
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
                    Paragraph(Text("If the real dimension of the entire kernel of Phi is at most one, then original mixed-state zero gluing is equivalent to the entire base being a simplex. The zero-nullity branch constructs least coordinate effects against all confirmers. In the nonzero one-dimensional branch, a globally minimal nonzero relation coefficient is oriented positively. Extremality excludes a relation with a single vertex on either sign side. Full-kernel-annihilating original effects exclude each negative vertex separately. Original midpoint gluing supplies a common effect at a midpoint; nonnegativity makes that effect vanish at both endpoints, hence at every convex combination. This gives convexity of the actual exclusion set without assuming general infimum attainment. The same relation forces a positive lower bound at the source barycenter, contradicting any excluding effect. The normalized weighted theorem supplies the sharper attained partition values on the same original objects."))), DescribeRole.Theorem))));
}

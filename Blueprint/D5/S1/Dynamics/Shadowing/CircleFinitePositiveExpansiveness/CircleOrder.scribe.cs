using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness;

internal sealed class CircleFinitePositiveExpansivenessCircleOrderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-target accessibility through actual full or proper iterate images on the circle.",
        H("CircleFinitePositiveExpansiveness - CircleOrder"), Blocks(
        Describe.Lean(DescribeId.Create("return-open-chain"), DeclarationHandle.Create(Owner + "return_open_chain_dense"),
            H("Connected dense open return chains"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A nondegenerate overlap of a proper arc and a positive return image propagates through finite-fibre iterates to overlapping arc interiors. Their union is connected and dense: a proper compact closure would trap a nondegenerate arc and contradict the interval obstruction. The return and proper-image assumptions are explicit helper hypotheses, proved when this helper is used in the two-target bridge."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("two-target-crossing"), DeclarationHandle.Create(Owner + "two_target_crossing"),
            H("A genuine lifted crossing of one of two targets"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every continuous finitely positively expansive circle selfmap, every nondegenerate proper arc and any two distinct circle points, some iterate has a continuous real lift whose values on the source segment lie strictly below and strictly above a representative of one target. The full-image case has lifted width at least one and can miss at most one target at a seam. In the proper-image case, late separated images, finite circle packing and nondegenerate overlaps yield the connected dense open return chain. A connected dense circle set cannot omit two points. Interior target membership then gives the actual lifted crossing; density alone is not substituted for crossing."))), DescribeRole.Theorem))));
}

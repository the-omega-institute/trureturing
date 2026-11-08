using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness;

internal sealed class CircleFinitePositiveExpansivenessBasicDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quotient-metric circle arcs, exact pullbacks, small crossings and strict turns.",
        H("CircleFinitePositiveExpansiveness - Basic"), Blocks(
        Describe.Lean(DescribeId.Create("proper-circle-arc"), DeclarationHandle.Create(Owner + "arc_of_compact_connected"),
            H("Proper compact connected circle sets are arcs"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Circle is the entire AddCircle (1 : Real) with its quotient metric. Arc is an actual projected nondegenerate real segment of length less than one. A compact connected infinite proper circle subset is represented by such an arc after cutting at a missing point. Trapping an arc under a positive iterate contradicts the interval obstruction via an actual compact embedding and a uniformly continuous injective semiconjugacy."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("two-lifted-turns"), DeclarationHandle.Create(Owner + "two_distinct_lifted_turns"),
            H("Two genuine turns from failure of local injectivity"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Under continuity and the uniform finite all-time bound, failure of local injectivity produces two distinct actual circle points at strict extrema of a continuous real lift. Finite fibres isolate extrema. If no second turn exists, the complementary interval restriction is injective and monotone; the lift translation identity from covering uniqueness contradicts the translated first extremum. No degree, orientation or local injectivity is assumed."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("short-arc-image"), DeclarationHandle.Create(Owner + "image_shortArc"),
            H("Exact transport of a short arc"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If a continuous circle map is injective on the actual short arc from x to y and its image remains within distance 1/8 of f(x), that image equals the short arc from f(x) to f(y). Quotient coordinates and interval monotonicity prove the equality; this supplies the final all-time arc induction."))), DescribeRole.Theorem)))));
}

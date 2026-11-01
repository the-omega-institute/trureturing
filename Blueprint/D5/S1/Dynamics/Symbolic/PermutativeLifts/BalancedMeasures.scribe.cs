using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedMeasuresDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invariant probabilities and finite cyclic phases of the actual balanced subshift.",
        H("Actual phase factors and invariant measures"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase"), DeclarationHandle.Create(Owner + "phase"),
                H("Physical phase"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A point of the compact balanced subshift has a unique marked tiling at every level. Its phase is the offset at zero, regarded as a residue modulo the common word height. Continuity follows from continuity of the actual decoder and the discrete tile-state space. Translation by any signed integer adds that integer to the phase."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("existence"), DeclarationHandle.Create(Owner + "exists_balanced_invariant_probability"),
                H("Existence of an invariant probability"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shift restricts to a continuous self-map of the nonempty compact Hausdorff balanced subshift. Applying Mathlib's Krylov--Bogolyubov theorem gives a Borel probability preserved by the one-step shift. This is an invariant measure on the actual point space, with no abstract tower or incidence-vector hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-fibres"), DeclarationHandle.Create(Owner + "phase_fiber_measure"),
                H("Uniform phase marginal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any invariant probability, adjacent phase fibres have equal mass because the one-step shift adds one to phase. Every cyclic residue is a nonnegative iterate of zero. The complete finite fibre partition has total mass one, so each fibre has mass 1/h(n). Consequently a finite phase set has its cardinality divided by h(n) as its exact mass."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("window-determined"), DeclarationHandle.Create(Owner + "WindowDetermined"),
                H("Finite-window events"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An event is determined by a signed finite window when any two actual points agreeing throughout that window have the same event membership. This allows arbitrary sets of finite-coordinate assignments, including the empty event, rather than only a single prescribed word."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("squeeze"), DeclarationHandle.Create(Owner + "window_event_measure_squeeze"),
                H("A common counting interval"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Declare a phase good when its entire actual fibre belongs to the event. The union of good fibres lies inside the event. Outside the sparse translated disagreement set, any two points with the same phase agree on the entire window, including all seams; hence every event point outside the exceptional phases belongs to a good fibre. Uniform phase mass bounds the event mass between the good-phase fraction and that fraction plus the exceptional-phase fraction, simultaneously for every invariant probability. No representative is selected in any phase fibre."))), DescribeRole.Theorem))));
}

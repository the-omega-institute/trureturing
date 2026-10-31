using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedUniqueErgodicDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedUniqueErgodic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique ergodicity of the actual recognizable balanced factorial subshift.",
        H("Vanishing phase error and unique ergodicity"),
        Blocks(
            Describe.Lean(DescribeId.Create("error"), DeclarationHandle.Create(Owner + "window_event_measure_difference_le"),
                H("A quantitative comparison"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any two invariant probabilities on the actual balanced subshift, their masses on an event determined by a signed window of length r differ by at most r/3^n at every level n. Both masses lie in the same good-phase counting interval, and its width is bounded by the exact disagreement identity for the literal balanced words."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-window-equality"), DeclarationHandle.Create(Owner + "window_event_measure_eq"),
                H("Equality on finite observations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The geometric error tends to zero as the phase level tends to infinity. The two invariant probabilities therefore give exactly the same mass to every event determined by a finite signed window. The window itself is fixed while the recognizing tile height grows."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniqueness"), DeclarationHandle.Create(Owner + "balanced_invariant_probability_unique"),
                H("Equality of the actual measures"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any finite set of integer coordinates fits inside a finite signed interval. Every measurable cylinder in the ambient full shift therefore pulls back to a finite-window event. Push both probabilities through the measurable subtype inclusion, apply Mathlib's existing generating cylinder pi-system to identify the ambient measures, and use injectivity of the pushforward along the measurable embedding to recover equality on actual balanced points."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unique-ergodicity"), DeclarationHandle.Create(Owner + "balanced_unique_ergodic"),
                H("The unique invariant probability"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combining actual invariant-probability existence with uniqueness proves that exactly one probability measure on the balanced point space is preserved by the one-step shift. This establishes unique ergodicity of this concrete compact subshift. Minimality, Toeplitz points, finite-group cocycles, and claims about a published open problem belong to their separate proof steps."))), DescribeRole.Theorem))));
}

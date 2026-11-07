using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class PreparedFiniteAdaptiveFrontierResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/PreparedFiniteAdaptiveFrontierResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank descent from adaptive semantic frontier responses",
        H("Rank descent from adaptive semantic frontier responses"),
        Blocks(
            Paragraph(Text("The abstract replay has arbitrary coordinate, finite value, symmetry and cache types. Its validity predicate depends on remaining fuel, cache and partial assignment. A valid cache lower bound, validity-preserving split updates, score-preserving actions and strictly rank-reducing domination are explicit hypotheses.")),
            Paragraph(Text("Each marked frontier context supplies a smaller bad event for every compatible event below the gap. Unmarked bound, symmetry and split nodes follow the original checker. The global conclusion additionally requires a valid initial cache, empty partial assignment and a successful root check.")),
            Node("checked-forces-smaller-bad-event", "checked_forces_smaller_bad_event", "Descend from a checked bad event",
                "Given the full checker inputs, validity of that exact fuel/cache/partial context, checker acceptance, compatibility and score below the gap, obtain another event below the gap with smaller natural rank. Fuel induction handles a frontier response directly, contradicts a bound leaf, applies a symmetry action, or follows the split child at the actual event value. The split hypothesis and checker range over every value.", DescribeRole.Theorem),
            Node("checked-global-lower-bound", "checked_global_lower_bound", "Exclude all events below the gap",
                "Under the same lower-bound, step, symmetry and response hypotheses, acceptance at the valid initial cache and empty partial assignment implies that every event has score at least the gap. Strong induction on natural rank excludes the smaller bad event produced by checked_forces_smaller_bad_event.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

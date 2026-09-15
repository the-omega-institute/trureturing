using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.InformationTemplateDebtStoreTests;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateBindingRuleTests
{
    private static readonly InformationTemplateActivation Active = new(Seed, true);
    private static readonly InformationTemplateDebtRow Debt = Read();
    private static readonly InformationOccurrenceKey A = Debt.Key;
    private static readonly InformationOccurrenceKey B = A with { Theorem = "Fixture.theorem_b" };
    private static readonly ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Empty =
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow>.Empty;

    private static RepositorySnapshot Tree(string source = Source, string? activation = null) => Snapshot(
        ("Registration.lean", source), (InformationTemplateDebtStore.ActivationPath, activation ??
            Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteActivation(Active).AsSpan())));

    private static ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Rows(params InformationOccurrenceKey[] keys) =>
        keys.ToImmutableDictionary(key => key, key => Debt with { Key = key });

    private static InformationTemplateOccurrence Occurrence(InformationOccurrenceKey key,
        InformationTemplateBindingState state = InformationTemplateBindingState.DeclaredValidated) => new(
            key, "Registration.lean", Debt.StatementIdentity, Debt.ContentInputs, state,
            state == InformationTemplateBindingState.DeclaredValidated ? new string('a', 64) : null,
            state == InformationTemplateBindingState.DeclaredUnresolved ? "IE-C050 reason=unclassified_form" : null,
            state == InformationTemplateBindingState.Undeclared ? null : "Binding.lean");

    private static InformationTemplateUniverse Universe(params InformationTemplateOccurrence[] occurrences) => new(
        occurrences.ToImmutableDictionary(o => o.Key), occurrences.Select(o => o.Key).ToImmutableHashSet(),
        ImmutableHashSet.Create("Registration.lean"), ImmutableHashSet.Create("Registration.lean"));

    private static ImmutableArray<DeclaredTemplateFinding> Evaluate(
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> beforeDebt,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> afterDebt,
        InformationTemplateUniverse before, InformationTemplateUniverse after,
        string[]? changed = null, RepositorySnapshot? candidate = null,
        Action<InformationOccurrenceKey>? observer = null) =>
        DeclaredTemplateBindingRule.Evaluate(Active, Tree(), candidate ?? Tree(), beforeDebt, afterDebt,
            before, after, (changed ?? []).ToHashSet(StringComparer.Ordinal), observer);

    [Fact]
    public void new_undeclared_occurrence_blocked()
    {
        var findings = Evaluate(Empty, Empty, Universe(), Universe(Occurrence(A, InformationTemplateBindingState.Undeclared)));
        Assert.Contains(findings, f => f.Code == "DTR-New");
    }

    [Fact]
    public void new_validated_occurrence_accepted() =>
        Assert.Empty(Evaluate(Empty, Empty, Universe(), Universe(Occurrence(A))));

    [Fact]
    public void equal_count_debt_swap_blocked()
    {
        var before = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared));
        var after = Universe(Occurrence(A), Occurrence(B, InformationTemplateBindingState.Undeclared));
        Assert.Contains(Evaluate(Rows(A), Rows(B), before, after), f => f.Code == "DTR-Subset");
    }

    [Fact]
    public void true_subset_debt_accepted()
    {
        var before = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared), Occurrence(B, InformationTemplateBindingState.Undeclared));
        var after = Universe(Occurrence(A), Occurrence(B, InformationTemplateBindingState.Undeclared));
        Assert.Empty(Evaluate(Rows(A, B), Rows(B), before, after));
    }

    [Fact]
    public void touched_debt_without_discharge_blocked()
    {
        var universe = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared));
        Assert.Contains(Evaluate(Rows(A), Rows(A), universe, universe, ["Registration.lean"], Tree(Source + "-- changed\n")),
            f => f.Code == "DTR-Touched");
    }

    [Fact]
    public void shared_content_dependency_touches_debt()
    {
        const string path = "Shared.lean";
        var input = new InformationTemplateContentInput(path, InformationTemplateJson.Sha256(Encoding.UTF8.GetBytes("old\n")));
        var rows = Rows(A, B).ToImmutableDictionary(kv => kv.Key, kv => kv.Value with { ContentInputs = [input] });
        var universe = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared), Occurrence(B, InformationTemplateBindingState.Undeclared));
        var baseline = Snapshot((InformationTemplateDebtStore.ActivationPath,
            Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteActivation(Active).AsSpan())), (path, "old\n"));
        var candidate = Snapshot((InformationTemplateDebtStore.ActivationPath,
            Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteActivation(Active).AsSpan())), (path, "new\n"));
        Assert.Contains(DeclaredTemplateBindingRule.Evaluate(Active, baseline, candidate, rows, rows,
            universe, universe, new HashSet<string> { path }), f => f.Code == "DTR-Touched");
    }

    [Fact]
    public void judge_only_change_preserves_untouched_debt()
    {
        var universe = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared));
        Assert.Empty(Evaluate(Rows(A), Rows(A), universe, universe, ["lean-report-inputs.json"]));
    }

    [Fact]
    public void strict_content_discharge_accepted()
    {
        var before = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared));
        Assert.Empty(Evaluate(Rows(A), Empty, before, Universe(Occurrence(A)), ["Binding.lean"]));
    }

    [Fact]
    public void premature_last_row_deletion_blocked()
    {
        var universe = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared));
        Assert.Contains(Evaluate(Rows(A), Empty, universe, universe), f => f.Code == "DTR-Residual");
    }

    [Fact]
    public void registration_deletion_does_not_discharge()
    {
        var before = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared));
        Assert.Contains(Evaluate(Rows(A), Empty, before, Universe()), f => f.Code == "DTR-Inventory");
    }

    [Fact]
    public void zero_debt_selects_whole_tree()
    {
        // Independently fixed keys include an unchanged occurrence outside delta.
        // This observes authoritative consumer invocations, not a returned count.
        var expected = new HashSet<InformationOccurrenceKey> { A, B };
        var observed = new HashSet<InformationOccurrenceKey>();
        var universe = Universe(Occurrence(A), Occurrence(B));
        Assert.Empty(Evaluate(Empty, Empty, universe, universe, ["Unrelated.lean"],
            observer: key => observed.Add(key)));
        Assert.True(expected.SetEquals(observed), "[FAIL] zero_debt_selects_whole_tree");
    }

    [Fact]
    public void zero_debt_empty_registry_blocked()
    {
        var before = Universe(Occurrence(A));
        var after = before with { Occurrences = ImmutableDictionary<InformationOccurrenceKey, InformationTemplateOccurrence>.Empty };
        Assert.Contains(Evaluate(Empty, Empty, before, after), f => f.Code == "DTR-Inventory");
    }

    [Fact]
    public void zero_debt_complete_tree_accepted()
    {
        var universe = Universe(Occurrence(A), Occurrence(B));
        Assert.Empty(Evaluate(Empty, Empty, universe, universe));
    }

    [Fact]
    public void inventory_hidden_root_rejected()
    {
        var universe = Universe(Occurrence(A));
        Assert.Contains(Evaluate(Empty, Empty, universe, universe with { AssessedSources = [] }), f => f.Code == "DTR-Inventory");
    }

    [Fact]
    public void inventory_first_freeze_selected()
    {
        var universe = Universe(Occurrence(A, InformationTemplateBindingState.Undeclared));
        Assert.Contains(Evaluate(Rows(A), Rows(A), universe, universe,
            ["Golden/Frozen/state/Registration.lean.json"]), f => f.Code == "DTR-Touched");
    }

    [Fact]
    public void declared_template_mechanism_deletion_rejected()
    {
        var universe = Universe(Occurrence(A));
        Assert.Contains(Evaluate(Empty, Empty, universe, universe, candidate: Snapshot()), f => f.Code == "DTR-Required");
    }

    [Fact]
    public void active_candidate_cannot_deactivate_or_retarget()
    {
        var universe = Universe(Occurrence(A));
        var changed = Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteActivation(Active with { Activated = false }).AsSpan());
        Assert.Contains(Evaluate(Empty, Empty, universe, universe, candidate: Tree(activation: changed)), f => f.Code == "DTR-Activation");
    }

    [Fact]
    public void inactive_declaration_migration_rejected()
    {
        var inactive = Active with { Activated = false };
        var bytes = Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteActivation(inactive).AsSpan());
        Assert.Contains(DeclaredTemplateBindingRule.Evaluate(inactive, Tree(activation: bytes), Tree(activation: bytes),
            Rows(A), Empty, Universe(Occurrence(A, InformationTemplateBindingState.Undeclared)), Universe(Occurrence(A)),
            new HashSet<string> { "Binding.lean" }), f => f.Code == "DTR-Activation");
    }
}

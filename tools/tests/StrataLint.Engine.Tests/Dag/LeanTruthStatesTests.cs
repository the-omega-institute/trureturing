using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Engine.Tests;

public sealed class LeanTruthStatesTests
{
    [Fact]
    public void StandardAxiomAlphabetIsPinned()
    {
        Assert.Equal(
            new[] { "Classical.choice", "Quot.sound", "propext" },
            LeanAxiomFacts.StandardAxioms.Order(StringComparer.Ordinal));
    }

    [Fact]
    public void DerivesClosedOpenAndTailStatesOnlyFromRepositoryAndLeanFacts()
    {
        const string closed = "D5/S0/Carrier/ClosedFact.lean";
        const string frontier = "D5/X_Frontier/OpenProblem.lean";
        const string sorry = "D5/S0/Carrier/SorryFact.lean";
        const string task = "D5/S0/Carrier/TaskFact.lean";
        const string debt = "D5/X_Assumptions/AxiomDebt.lean";
        const string conditional = "D5/X_Certificates/ConditionalResult.lean";
        const string semantic = "Blueprint/D5/S0/Carrier/ClosedFact.md";
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [closed] = "theorem closedFact : True := True.intro\n",
            [frontier] = "def openProblem : Nat := 0\n",
            [sorry] = "theorem sorryFact : True := by sorry\n",
            [task] = "/- TASK D5-T9999 -/\ndef taskFact : Nat := 0\n",
            [debt] = "axiom registeredDebt : False\n",
            [conditional] = "theorem conditionalResult : False := registeredDebt\n",
            [semantic] = "# Closed fact\n",
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [closed] = StateReport(declarations: [StateDeclaration("closedFact", "propext", "Classical.choice", "Quot.sound")]),
            [frontier] = StateReport(),
            [sorry] = StateReport(declarations: [StateDeclaration("sorryFact", "sorryAx")]),
            [task] = StateReport(),
            [debt] = StateReport(declarations: [StateDeclaration("registeredDebt", "registeredDebt", kind: "axiom")]),
            [conditional] = StateReport(
                imports: ["D5.X_Assumptions.AxiomDebt"],
                declarations: [StateDeclaration("conditionalResult", "registeredDebt")]),
        };

        var (snapshot, closure) = ValidatedStateFixture(files, reports);
        var states = LeanTruthStates.Resolve(snapshot, closure);

        Assert.Equal(TruthState.Closed, states[Path(closed)]);
        Assert.Equal(TruthState.Open, states[Path(frontier)]);
        Assert.Equal(TruthState.Open, states[Path(sorry)]);
        Assert.Equal(TruthState.Open, states[Path(task)]);
        Assert.Equal(TruthState.Tail, states[Path(debt)]);
        Assert.Equal(TruthState.Tail, states[Path(conditional)]);
        Assert.DoesNotContain(states.Keys, path => path.Value == semantic);
        Assert.Equal(6, states.Count);
    }

    [Fact]
    public void ManagedInputIdentityIgnoresDigestionLedgerAndCasChanges()
    {
        const string leanPath = "D5/S0/Carrier/ClosedFact.lean";
        var before = Decode(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [leanPath] = "theorem closedFact : True := True.intro\n",
            ["Meta/Digestion/backfill/source/open-open/atom.yaml"] = "projected_status = \"open-open\"\n",
        });
        var after = Decode(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [leanPath] = "theorem closedFact : True := True.intro\n",
            ["Meta/Digestion/backfill/source/closed-closed/atom.yaml"] = "projected_status = \"closed-closed\"\n",
            ["Meta/Digestion/atoms/sha256/abc"] = "canonical atom bytes\n",
        });

        LeanTruthStates.RequireSameManagedInputs(before, after);
    }

    [Fact]
    public void ManagedInputIdentityRejectsLeanByteChanges()
    {
        const string leanPath = "D5/S0/Carrier/ClosedFact.lean";
        var before = Decode(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [leanPath] = "theorem closedFact : True := True.intro\n",
        });
        var after = Decode(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [leanPath] = "theorem closedFact : 1 = 1 := rfl\n",
        });

        var exception = Assert.Throws<InvalidOperationException>(
            () => LeanTruthStates.RequireSameManagedInputs(before, after));

        Assert.Contains(leanPath, exception.Message, StringComparison.Ordinal);
    }

    private static (RepositorySnapshot Snapshot, AcceptedLeanClosure Closure) ValidatedStateFixture(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        return (snapshot, closure);
    }

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static RepoPath Path(string value) =>
        RepoPath.TryCreate(value, out var path)
            ? path
            : throw new InvalidOperationException("test path is invalid");

    private static LeanFileReport StateReport(
        IEnumerable<string>? imports = null,
        IEnumerable<LeanDeclaration>? declarations = null) =>
        new(
            (imports ?? Array.Empty<string>()).ToImmutableArray(),
            (declarations ?? Array.Empty<LeanDeclaration>()).ToImmutableArray());

    private static LeanDeclaration StateDeclaration(
        string name,
        string axiom,
        string? secondAxiom = null,
        string? thirdAxiom = null,
        string kind = "theorem") =>
        new(
            name,
            kind,
            "True",
            new[] { axiom, secondAxiom, thirdAxiom }
                .OfType<string>()
                .ToImmutableArray());
}

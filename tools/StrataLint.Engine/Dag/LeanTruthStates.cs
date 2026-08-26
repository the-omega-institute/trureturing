using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

public enum TruthState
{
    Closed,
    Open,
    Tail,
    Semantic,
}

public static class LeanAxiomFacts
{
    public static ImmutableHashSet<string> StandardAxioms { get; } =
        ImmutableHashSet.Create(StringComparer.Ordinal, "propext", "Classical.choice", "Quot.sound");

    public static bool IsStandard(string axiom) => StandardAxioms.Contains(axiom);
}

public static class LeanTruthStates
{
    private static readonly Regex TaskTokenPattern = new(
        "(?:^|[^A-Za-z0-9_])TASK\\s+D[0-9]+-T[0-9]{4}(?:[^A-Za-z0-9_]|$)",
        RegexOptions.CultureInvariant);

    public static ImmutableDictionary<RepoPath, TruthState> Resolve(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);

        return snapshot.Files.Keys
            .Where(static path => LeanClosureValidator.IsManagedLean(path.Value))
            .ToImmutableDictionary(
                static path => path,
                path => DeriveState(snapshot.Files[path], lean.Report));
    }

    internal static void RequireSameManagedInputs(
        RepositorySnapshot derivedFrom,
        RepositorySnapshot consumingSnapshot)
    {
        ArgumentNullException.ThrowIfNull(derivedFrom);
        ArgumentNullException.ThrowIfNull(consumingSnapshot);

        var derivedInputs = derivedFrom.Files
            .Where(static item => LeanClosureValidator.IsManagedLean(item.Key.Value))
            .ToDictionary(static item => item.Key, static item => item.Value.RawBytes);
        var consumingInputs = consumingSnapshot.Files
            .Where(static item => LeanClosureValidator.IsManagedLean(item.Key.Value))
            .ToDictionary(static item => item.Key, static item => item.Value.RawBytes);
        var mismatch = derivedInputs.Keys
            .Union(consumingInputs.Keys)
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .FirstOrDefault(path =>
                !derivedInputs.TryGetValue(path, out var derivedBytes)
                || !consumingInputs.TryGetValue(path, out var consumingBytes)
                || !derivedBytes.AsSpan().SequenceEqual(consumingBytes.AsSpan()));
        if (mismatch is not null)
        {
            throw new InvalidOperationException(
                $"precomputed truth states do not match managed Lean input {mismatch.Value}");
        }
    }

    private static TruthState DeriveState(
        RepositoryFile file,
        LeanAxiomReport report)
    {
        var leanFile = report.Files[file.Path];
        if (file.Path.Value.Contains("/X_Frontier/", StringComparison.Ordinal)
            || TaskTokenPattern.IsMatch(file.Text)
            || leanFile.Declarations.Any(static declaration =>
                declaration.Axioms.Contains("sorryAx", StringComparer.Ordinal)))
        {
            return TruthState.Open;
        }

        if (file.Path.Value.Contains("/X_Assumptions/", StringComparison.Ordinal)
            || leanFile.Declarations.Any(static declaration => declaration.Kind == "axiom")
            || leanFile.Declarations.SelectMany(static declaration => declaration.Axioms)
                .Any(static axiom => axiom != "sorryAx" && !LeanAxiomFacts.IsStandard(axiom)))
        {
            return TruthState.Tail;
        }

        return TruthState.Closed;
    }
}

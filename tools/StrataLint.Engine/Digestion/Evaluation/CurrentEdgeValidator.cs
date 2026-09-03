namespace StrataLint.Engine;

internal sealed record CurrentEdgeValidation(
    bool IsResolved,
    bool IsClosed,
    RepositoryFile? Target,
    TruthState State,
    string? Code,
    string Detail,
    string Diagnostic)
{
    internal DigestionGap? ResolutionGap => IsResolved
        ? null
        : new DigestionGap(Code!, Detail, DigestionGapSeverity.NonFatal);
}

internal static class CurrentEdgeValidator
{
    internal static CurrentEdgeValidation Validate(
        string gidText,
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        IReadOnlyDictionary<RepoPath, TruthState> truthStates)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(gidText);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(truthStates);

        if (!Gid.TryParse(gidText, out var gid)
            || !snapshot.TryGetFile(gid.Path.Value, out var target))
        {
            return Rejected(
                "target-gid-missing",
                gidText,
                $"current edge GID {gidText} does not resolve to a current repository target");
        }

        if (gid.ToTarget() is Target.Formal { Declaration: { } declaration } formal)
        {
            var matches = report.Files.TryGetValue(formal.Path, out var module)
                && string.IsNullOrEmpty(module.Error)
                    ? module.Declarations.Count(candidate =>
                        string.Equals(candidate.Name, declaration, StringComparison.Ordinal)
                        || candidate.Name.EndsWith("." + declaration, StringComparison.Ordinal))
                    : 0;
            if (matches != 1)
            {
                return Rejected(
                    matches == 0
                        ? "target-declaration-missing"
                        : "target-declaration-ambiguous",
                    gidText,
                    $"current edge GID {gidText} resolves to {matches} report declarations");
            }
        }

        var state = truthStates.TryGetValue(target.Path, out var resolvedState)
            ? resolvedState
            : TruthState.Semantic;
        var isClosed = state == TruthState.Closed;
        var code = isClosed ? null : $"lean-state-{state.ToString().ToLowerInvariant()}";
        return new CurrentEdgeValidation(
            IsResolved: true,
            IsClosed: isClosed,
            target,
            state,
            code,
            gidText,
            isClosed
                ? string.Empty
                : $"current edge GID {gidText} is {code}; the current report module must be Closed");
    }

    private static CurrentEdgeValidation Rejected(
        string code,
        string detail,
        string diagnostic) =>
        new(
            IsResolved: false,
            IsClosed: false,
            Target: null,
            TruthState.Semantic,
            code,
            detail,
            diagnostic);
}

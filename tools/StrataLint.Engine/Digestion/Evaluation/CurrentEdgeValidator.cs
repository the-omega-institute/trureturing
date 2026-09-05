namespace StrataLint.Engine;

internal sealed record CurrentEdgeValidation(
    bool IsResolved,
    bool IsClosed,
    RepositoryFile? Target,
    string? TargetStatementId,
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
        IReadOnlyDictionary<RepoPath, TruthState> truthStates,
        FrozenStatementIndex frozenStatements)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(gidText);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(truthStates);
        ArgumentNullException.ThrowIfNull(frozenStatements);

        if (!Gid.TryParse(gidText, out var gid)
            || !snapshot.TryGetFile(gid.Path.Value, out var target))
        {
            return Rejected(
                "target-gid-missing",
                gidText,
                $"current edge GID {gidText} does not resolve to a current repository target");
        }

        if (!frozenStatements.TryResolve(
                gid,
                out var statementId,
                out var resolutionError,
                out var resolutionFailure))
        {
            return Rejected(
                resolutionFailure switch
                {
                    FrozenStatementResolutionFailure.MissingDeclaration =>
                        "target-declaration-missing",
                    FrozenStatementResolutionFailure.AmbiguousDeclaration =>
                        "target-declaration-ambiguous",
                    _ => "target-statement-unresolved",
                },
                gidText,
                $"current edge GID {gidText} has no unique active frozen statement: {resolutionError}");
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
            statementId!.Value,
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
            TargetStatementId: null,
            TruthState.Semantic,
            code,
            detail,
            diagnostic);
}

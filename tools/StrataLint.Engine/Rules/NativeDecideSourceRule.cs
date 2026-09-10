using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class NativeDecideSourceRule
{
    internal static bool IsApplicable(RepositoryFile artifact, RuleApplicabilityContext context) =>
        IsD5Lean(artifact.Path);

    internal static bool IsAffectedBy(RuleEvaluationContext context) =>
        SelectedPaths(context.Current, context.Baseline, context.Changes).Any();

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
        SelectedPaths(context.Current, context.Baseline, context.Changes)
            .OrderBy(path => path.Value, StringComparer.Ordinal)
            .SelectMany(path => Inspect(context.Current, path, context.SourceContext)).ToImmutableArray();

    internal static ImmutableArray<RuleFinding> Inspect(RepositorySnapshot snapshot, RepoPath path,
        LeanSourceContextInput input)
    {
        var source = snapshot.Files[path].Text;
        var demanded = false;
        var absent = Scan(_ => { demanded = true; return false; });
        if (!demanded) return absent;
        var registered = Scan(_ => true);
        // Context-free findings survive unrelated grammar failure. Agreement of both
        // finite lexical projections needs no parser input at this boundary.
        if (absent.SequenceEqual(registered)) return absent;
        var certain = absent.Intersect(registered).ToImmutableArray();
        if (!certain.IsEmpty) return certain;
        try
        {
            var file = input.GetFile(snapshot, path, "current");
            return Scan(file.EqualityAt);
        }
        catch (LeanSourceExtractionException exception)
        {
            return [new(path.Value, $"NATIVE_DECIDE_CONTEXT_ERROR line={exception.Line ?? 1}: {exception.Message}")];
        }

        ImmutableArray<RuleFinding> Scan(Func<int, bool> equality)
        {
            var findings = ImmutableArray.CreateBuilder<RuleFinding>();
            try
            {
                LeanSourceTokenizer.TokenizeIncludingInterpolationTerms(source, equality, token =>
                {
                    if (token.Text == "native_decide") findings.Add(new(path.Value,
                        $"NATIVE_DECIDE_SOURCE line={token.Line}: bare native_decide token is forbidden in changed D5 Lean source"));
                });
            }
            catch (LeanSourceExtractionException exception)
            {
                findings.Add(new(path.Value,
                    $"NATIVE_DECIDE_LEXICAL_ERROR line={exception.Line ?? 1}: {exception.Message}"));
            }
            return findings.Distinct().ToImmutableArray();
        }
    }

    internal static IEnumerable<RepoPath> SelectedPaths(RepositorySnapshot current,
        RepositorySnapshot baseline, RawChangeSet changes) => changes.Paths.Distinct().Where(path =>
            IsD5Lean(path) && current.Files.TryGetValue(path, out var file)
            && (!baseline.Files.TryGetValue(path, out var old)
                || !file.RawBytes.AsSpan().SequenceEqual(old.RawBytes.AsSpan())));

    private static bool IsD5Lean(RepoPath path) => path.Value.StartsWith("D5/", StringComparison.Ordinal)
        && path.Value.EndsWith(".lean", StringComparison.Ordinal);
}

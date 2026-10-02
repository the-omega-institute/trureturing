using System.Collections.Immutable;

namespace StrataLint.Scribe;

public sealed record RelationVerificationItem(
    string Path, RelationReadFailure? Unreadable, ScribeScriptFailure? HostFailure, string? Difference);

public sealed record RelationVerificationResult(
    ImmutableArray<RelationVerificationItem> Items, TimeSpan StaticElapsed)
{
    public int Unreadable => Items.Count(static item => item.Unreadable is not null);
    public int HostFailures => Items.Count(static item => item.HostFailure is not null);
    public int Mismatches => Items.Count(static item => item.Difference is not null);

    public int Write(TextWriter output, TextWriter error)
    {
        output.WriteLine(FormattableString.Invariant(
            $"relations verify: paths={Items.Length} unreadable={Unreadable} hostFailures={HostFailures} mismatches={Mismatches}"));
        foreach (var item in Items)
        {
            if (item.Unreadable is { } unreadable)
                error.WriteLine($"Unreadable: {item.Path}: {unreadable.SourcePath}:{unreadable.Line}: {unreadable.Shape}: {unreadable.Detail}");
            if (item.HostFailure is { } hostFailure) error.WriteLine(hostFailure);
            if (item.Difference is { } difference) error.WriteLine($"RelationMismatch: {item.Path}: {difference}");
        }
        return Unreadable == 0 && HostFailures == 0 && Mismatches == 0 ? 0 : 1;
    }
}

public static class RelationVerifier
{
    public static RelationVerificationResult Verify(string repositoryRoot, IEnumerable<string> paths)
    {
        var selected = paths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
        var references = ScribeScriptHost.ReferenceAssemblies();
        var start = TimeProvider.System.GetTimestamp();
        var indexed = selected.Select(path => StaticRelationIndexer.ReadPrepared(repositoryRoot, path, references)).ToImmutableArray();
        var elapsed = TimeProvider.System.GetElapsedTime(start);
        var executed = ScribeScriptHost.ExecuteBatch(repositoryRoot, selected);
        return Compare(indexed, executed, elapsed);
    }

    internal static RelationVerificationResult Compare(
        ImmutableArray<RelationReadResult> indexed, ImmutableArray<ScribeScriptResult> executed, TimeSpan elapsed)
    {
        var hosts = executed.ToDictionary(static result => result.RelativePath, StringComparer.Ordinal);
        return new(indexed.Select(read =>
        {
            var host = hosts[read.RelativePath];
            string? difference = null;
            if (read.Projection is not null && host.IsSuccess)
            {
                var actual = RelationProjection.FromDefinition(host.Definition!);
                if (!read.Projection.Encode().AsSpan().SequenceEqual(actual.Encode()))
                    difference = read.Projection.FirstDifference(actual);
            }
            return new RelationVerificationItem(read.RelativePath, read.Failure, host.Failure, difference);
        }).ToImmutableArray(), elapsed);
    }
}

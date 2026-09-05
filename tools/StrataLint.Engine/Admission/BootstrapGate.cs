using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

public enum RawChangeKind
{
    Added,
    Modified,
    Deleted,
    Copied,
}

public sealed record RawChange(RepoPath Path, RawChangeKind Kind);

public sealed class RawChangeSet
{
    private readonly HashSet<string> exactPaths;

    private RawChangeSet(
        ImmutableArray<RawChange> entries,
        HashSet<string> exactPaths)
    {
        Entries = entries;
        Paths = entries.Select(static entry => entry.Path).ToImmutableArray();
        this.exactPaths = exactPaths;
    }

    public ImmutableArray<RawChange> Entries { get; }

    public ImmutableArray<RepoPath> Paths { get; }

    public bool ContainsPath(string path)
    {
        ArgumentNullException.ThrowIfNull(path);
        return exactPaths.Contains(path);
    }

    public static RawChangeSet Create(IEnumerable<string> paths) =>
        CreateWithKinds(paths.Select(static path => (path, RawChangeKind.Modified)));

    public static RawChangeSet CreateWithKinds(
        IEnumerable<(string Path, RawChangeKind Kind)> entries)
    {
        ArgumentNullException.ThrowIfNull(entries);
        var builder = ImmutableArray.CreateBuilder<RawChange>();
        var exact = new HashSet<string>(StringComparer.Ordinal);
        var folded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var (rawPath, kind) in entries)
        {
            if (!RepoPath.TryCreate(rawPath, out var path))
            {
                throw new ArgumentException($"Invalid raw changed path: {rawPath}", nameof(entries));
            }

            if (!exact.Add(path.Value) || !folded.Add(path.Value))
            {
                throw new ArgumentException(
                    $"Duplicate or case-colliding changed path: {path.Value}",
                    nameof(entries));
            }

            builder.Add(new RawChange(path, kind));
        }

        return new RawChangeSet(builder.ToImmutable(), exact);
    }
}

public sealed class MetaChangeSet
{
    internal MetaChangeSet(ImmutableArray<RepoPath> paths) => Paths = paths;

    public ImmutableArray<RepoPath> Paths { get; }
}

public sealed class MetaClear
{
    private MetaClear() { }

    internal static MetaClear Create() => new();
}

internal sealed class MetaEvaluationProfile
{
    private MetaEvaluationProfile(MetaClear? clearCapability, MetaChangeSet? protectedChangeSet)
    {
        ClearCapability = clearCapability;
        ProtectedChangeSet = protectedChangeSet;
    }

    internal MetaClear? ClearCapability { get; }

    internal MetaChangeSet? ProtectedChangeSet { get; }

    internal static MetaEvaluationProfile ForClear(MetaClear capability) =>
        new(capability ?? throw new ArgumentNullException(nameof(capability)), null);

    internal static MetaEvaluationProfile ForProtectedSurface(MetaChangeSet changeSet)
    {
        ArgumentNullException.ThrowIfNull(changeSet);
        if (changeSet.Paths.IsDefaultOrEmpty || changeSet.Paths.Any(static path => !BootstrapGate.IsProtected(path)))
        {
            throw new ArgumentException(
                "Protected-surface evaluation requires a non-empty protected change set.",
                nameof(changeSet));
        }

        return new MetaEvaluationProfile(null, changeSet);
    }
}

[Union(EnableImplicitConversions = false)]
public partial record BootstrapOutcome
{
    public partial record Clear
    {
        internal Clear(MetaClear capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public MetaClear Capability { get; }
    }

    public partial record ProtectedSurfaceVerificationRequired(MetaChangeSet ChangeSet);

    public partial record InfrastructureFailure(string Message);
}

public static class BootstrapGate
{
    internal const string ProtectedSurfaceMessage =
        "protected-surface change detected (SL-022)";
    public static BootstrapOutcome Evaluate(RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(changes);
        var protectedPaths = changes.Paths.Where(IsProtected).ToImmutableArray();
        return protectedPaths.Length == 0
            ? new BootstrapOutcome.Clear(MetaClear.Create())
            : new BootstrapOutcome.ProtectedSurfaceVerificationRequired(
                new MetaChangeSet(protectedPaths));
    }

    internal static ImmutableArray<Diagnostic> CreateSl022Diagnostics(MetaChangeSet changeSet)
    {
        ArgumentNullException.ThrowIfNull(changeSet);
        if (changeSet.Paths.IsDefaultOrEmpty
            || changeSet.Paths.Any(static path => !IsProtected(path)))
        {
            throw new ArgumentException(
                "SL-022 diagnostics require a non-empty protected change set.",
                nameof(changeSet));
        }

        // 按 Id 查,不按位置。位置会随目录里任何一条规则的增删而位移,
        // 而这个 descriptor 必须始终是 SL-022 本身。
        var descriptor = RuleCatalog.Default.Descriptors
            .Single(item => item.Id.Value == "SL-022");
        return changeSet.Paths
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => new Diagnostic(
                descriptor.Id,
                descriptor.Title,
                descriptor.DisplaySeverity,
                descriptor.AdmissionEffect,
                path.Value,
                ProtectedSurfaceMessage))
            .ToImmutableArray();
    }

    internal static bool IsProtected(RepoPath path) => BootstrapProtectionPolicy.IsProtected(path);
}

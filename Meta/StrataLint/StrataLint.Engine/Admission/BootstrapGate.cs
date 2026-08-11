using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

public sealed class RawChangeSet
{
    private RawChangeSet(ImmutableArray<RepoPath> paths) => Paths = paths;

    public ImmutableArray<RepoPath> Paths { get; }

    public static RawChangeSet Create(IEnumerable<string> paths)
    {
        ArgumentNullException.ThrowIfNull(paths);
        var builder = ImmutableArray.CreateBuilder<RepoPath>();
        var exact = new HashSet<string>(StringComparer.Ordinal);
        var folded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var rawPath in paths)
        {
            if (!RepoPath.TryCreate(rawPath, out var path))
            {
                throw new ArgumentException($"Invalid raw changed path: {rawPath}", nameof(paths));
            }

            if (!exact.Add(path.Value) || !folded.Add(path.Value))
            {
                throw new ArgumentException($"Duplicate or case-colliding changed path: {path.Value}", nameof(paths));
            }

            builder.Add(path);
        }

        return new RawChangeSet(builder.ToImmutable());
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
    internal const string SpecificationPath = "docs/develop/spec/golden-ledger-repo-spec.md";
    internal const string DefinitionsPathPrefix =
        "Meta/StrataLint/StrataLint.Definitions/";

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

        var descriptor = RuleCatalog.Default.Descriptors[21];
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

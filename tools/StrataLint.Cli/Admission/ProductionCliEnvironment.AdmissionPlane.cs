using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    private static readonly string[] AdmissionPlaneRepairPaths =
        [".github/workflows/ci.yml", FileMapLoader.RelativePath];
    // This gate runs before canonical FILEMAP validation so a malformed FILEMAP can repair
    // itself. Registering a post-canonical NoFindings stand-in would misstate enforcement.
    private static readonly RuleDescriptor AdmissionPlaneRule = new(
        RuleId.CreateKnown(29),
        "Admission plane partition",
        DisplaySeverity.Error,
        "repository",
        AdmissionEffect.Block,
        RuleLifecycle.Active,
        null);

    internal static AdmissionOutcome? EvaluateAdmissionPlane(
        RawRepositorySnapshot protectedBase,
        RawChangeSet changes,
        out bool usedBootstrap)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(changes);
        usedBootstrap = false;
        var changedPaths = AdmissionPlaneChangedPaths(changes);
        if (changedPaths.IsEmpty)
        {
            return null;
        }

        var isRepair = changedPaths.All(path =>
            AdmissionPlaneRepairPaths.Contains(path.Value, StringComparer.Ordinal));
        var fileMap = protectedBase.Entries.FirstOrDefault(
            static entry => entry.Path == FileMapLoader.RelativePath);
        if (fileMap is null)
        {
            usedBootstrap = isRepair;
            return isRepair
                ? null
                : Failure("protected-base FILEMAP is unavailable outside the repair boundary");
        }

        AdmissionPlaneFileMap manifest;
        try
        {
            manifest = AdmissionPlaneFileMapLoader.Parse(
                fileMap.Bytes.AsSpan(),
                $"protected-base:{FileMapLoader.RelativePath}");
        }
        catch (FileMapParseException exception)
        {
            usedBootstrap = isRepair;
            return isRepair
                ? null
                : Failure($"protected-base FILEMAP cannot be parsed: {exception.Message}");
        }
        catch (FileMapPatternException exception)
        {
            return Failure($"{FileMapPatternException.FindingCode}: {exception.Message}");
        }
        catch (FormatException exception)
        {
            return Failure(exception.Message);
        }

        var hasJudgePath = false;
        var hasContentPath = false;
        foreach (var path in changedPaths)
        {
            var matches = manifest.Match(path.Value);
            if (matches is not [var match])
            {
                return Failure(
                    "changed path must match exactly one protected-base FILEMAP entry; "
                    + $"path={path.Value} matches={matches.Length}");
            }

            hasJudgePath |= match.AdmissionPlane is FileMapAdmissionPlane.Judge;
            hasContentPath |= match.AdmissionPlane is FileMapAdmissionPlane.Content;
        }

        if (isRepair)
        {
            var invalid = AdmissionPlaneRepairPaths.FirstOrDefault(path =>
                manifest.Match(path) is not [{ AdmissionPlane: FileMapAdmissionPlane.Judge }]);
            if (invalid is not null)
            {
                return Failure($"reserved repair path must resolve once to judge: {invalid}");
            }
        }

        return hasJudgePath && hasContentPath
            ? new AdmissionOutcome.RuleRejected(ImmutableArray.Create(new Diagnostic(
                AdmissionPlaneRule.Id,
                AdmissionPlaneRule.Title,
                AdmissionPlaneRule.DisplaySeverity,
                AdmissionPlaneRule.AdmissionEffect,
                FileMapLoader.RelativePath,
                "ADMISSION-PLANE-MIXED: judge and content paths cannot be submitted together")))
            : null;
    }

    private static ImmutableArray<RepoPath> AdmissionPlaneChangedPaths(RawChangeSet changes) =>
        changes.Entries
            .Where(static change => change.Kind switch
            {
                RawChangeKind.Added => true,
                RawChangeKind.Modified => true,
                RawChangeKind.Deleted => true,
                RawChangeKind.Copied => false,
                _ => throw new InvalidOperationException(
                    $"unsupported raw change kind: {change.Kind}"),
            })
            .Select(static change => change.Path)
            .ToImmutableArray();

    private static AdmissionOutcome.InfrastructureFailure Failure(string message) => new(message);

    private static RawRepositorySnapshot WithoutFileMap(RawRepositorySnapshot snapshot) =>
        RawRepositorySnapshot.Create(snapshot.Entries.Where(
            static entry => entry.Path != FileMapLoader.RelativePath));
}

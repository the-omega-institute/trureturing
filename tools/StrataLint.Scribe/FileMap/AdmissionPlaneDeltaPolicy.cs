using StrataLint.Engine;

namespace StrataLint.Scribe;

internal enum AdmissionPlaneDeltaClassification
{
    Empty,
    JudgeOnly,
    ContentOnly,
    Bootstrap,
    Mixed,
}

internal sealed record AdmissionPlaneDeltaDecision(
    bool IsAdmissible,
    AdmissionPlaneDeltaClassification? Classification,
    string Code,
    string Path,
    string Message)
{
    internal bool RequiresFullEngineering()
    {
        if (!IsAdmissible || Classification is null)
        {
            throw new InvalidOperationException(
                "FULL routing requires an admissible admission-plane classification.");
        }

        return Classification is AdmissionPlaneDeltaClassification.JudgeOnly
            or AdmissionPlaneDeltaClassification.Bootstrap;
    }
}

internal static class AdmissionPlaneDeltaPolicy
{
    internal const string MixedCode = "ADMISSION-PLANE-MIXED";

    private const string BaseFileMapUnavailableCode =
        "ADMISSION-PLANE-BASE-FILEMAP-UNAVAILABLE";
    private const string BaseFileMapInvalidCode =
        "ADMISSION-PLANE-BASE-FILEMAP-INVALID";
    private const string MatchCountCode = "ADMISSION-PLANE-PATH-MATCH-COUNT";
    private const string RepairPathNotJudgeCode =
        "ADMISSION-PLANE-REPAIR-PATH-NOT-JUDGE";
    private const string CiPath = ".github/workflows/ci.yml";
    private static readonly string[] RepairPaths =
        [CiPath, FileMapLoader.RelativePath];

    internal static AdmissionPlaneDeltaDecision Evaluate(
        RepositorySnapshot protectedBase,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(changes);
        if (changes.Paths.IsEmpty)
        {
            return Admissible(AdmissionPlaneDeltaClassification.Empty);
        }

        return protectedBase.TryGetFile(FileMapLoader.RelativePath, out var fileMap)
            ? Evaluate(fileMap.RawBytes.AsSpan(), changes)
            : EvaluateUnavailable(changes);
    }

    internal static AdmissionPlaneDeltaDecision Evaluate(
        ReadOnlySpan<byte> protectedBaseFileMap,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(changes);
        if (changes.Paths.IsEmpty)
        {
            return Admissible(AdmissionPlaneDeltaClassification.Empty);
        }

        var isRepair = IsRepair(changes);
        FileMapManifest manifest;
        try
        {
            manifest = FileMapLoader.Parse(
                protectedBaseFileMap,
                $"protected-base:{FileMapLoader.RelativePath}");
        }
        catch (FileMapAdmissionPlaneException exception)
        {
            return Failed(exception.Code, exception.Path, exception.Message);
        }
        catch (FileMapPatternException exception)
        {
            return Failed(
                FileMapPatternException.FindingCode,
                exception.Pattern,
                exception.Message);
        }
        catch (FormatException exception)
        {
            return isRepair
                ? Admissible(AdmissionPlaneDeltaClassification.Bootstrap)
                : Failed(
                    BaseFileMapInvalidCode,
                    FileMapLoader.RelativePath,
                    exception.Message);
        }

        var judgePaths = new List<string>();
        var contentPaths = new List<string>();
        foreach (var path in changes.Paths)
        {
            var matches = manifest.Match(path.Value);
            if (matches.Length != 1)
            {
                return Failed(
                    MatchCountCode,
                    path.Value,
                    $"changed path must match exactly one protected-base FILEMAP entry; "
                    + $"path={path.Value} matches={matches.Length}");
            }

            if (matches[0].AdmissionPlane is FileMapAdmissionPlane.Judge)
            {
                judgePaths.Add(path.Value);
            }
            else
            {
                contentPaths.Add(path.Value);
            }
        }

        if (isRepair)
        {
            foreach (var repairPath in RepairPaths)
            {
                var matches = manifest.Match(repairPath);
                if (matches.Length != 1
                    || matches[0].AdmissionPlane is not FileMapAdmissionPlane.Judge)
                {
                    return Failed(
                        RepairPathNotJudgeCode,
                        repairPath,
                        $"reserved repair path must match exactly one judge-plane entry; "
                        + $"path={repairPath} matches={matches.Length}");
                }
            }
        }

        if (judgePaths.Count > 0 && contentPaths.Count > 0)
        {
            return new AdmissionPlaneDeltaDecision(
                false,
                AdmissionPlaneDeltaClassification.Mixed,
                MixedCode,
                FileMapLoader.RelativePath,
                $"judge and content paths cannot be submitted together; "
                + $"judge={judgePaths.Count} content={contentPaths.Count}");
        }

        return Admissible(
            judgePaths.Count > 0
                ? AdmissionPlaneDeltaClassification.JudgeOnly
                : AdmissionPlaneDeltaClassification.ContentOnly);
    }

    internal static AdmissionPlaneDeltaDecision EvaluateUnavailable(RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(changes);
        if (changes.Paths.IsEmpty)
        {
            return Admissible(AdmissionPlaneDeltaClassification.Empty);
        }

        return IsRepair(changes)
            ? Admissible(AdmissionPlaneDeltaClassification.Bootstrap)
            : Failed(
                BaseFileMapUnavailableCode,
                FileMapLoader.RelativePath,
                "protected-base FILEMAP is unavailable outside the reserved repair boundary");
    }

    private static bool IsRepair(RawChangeSet changes) =>
        changes.Paths.All(path => RepairPaths.Contains(path.Value, StringComparer.Ordinal));

    private static AdmissionPlaneDeltaDecision Admissible(
        AdmissionPlaneDeltaClassification classification) =>
        new(true, classification, string.Empty, string.Empty, string.Empty);

    private static AdmissionPlaneDeltaDecision Failed(
        string code,
        string path,
        string message) =>
        new(false, null, code, path, message);
}

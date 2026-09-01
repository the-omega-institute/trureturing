using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record TargetIdentity(string Assembly, string TestId);
internal sealed class TargetIdentityComparer : IEqualityComparer<TargetIdentity>
{
    internal static readonly TargetIdentityComparer Instance = new();

    public bool Equals(TargetIdentity? left, TargetIdentity? right) =>
        ReferenceEquals(left, right)
        || left is not null
            && right is not null
            && StringComparer.OrdinalIgnoreCase.Equals(left.Assembly, right.Assembly)
            && StringComparer.Ordinal.Equals(left.TestId, right.TestId);

    public int GetHashCode(TargetIdentity identity) => HashCode.Combine(
        StringComparer.OrdinalIgnoreCase.GetHashCode(identity.Assembly),
        StringComparer.Ordinal.GetHashCode(identity.TestId));
}
internal sealed record BlockerHintContract(int SchemaVersion, IReadOnlyList<TargetIdentity> Blockers);
internal sealed record TargetSetContract(
    int SchemaVersion,
    IReadOnlyList<TargetIdentity> RequiredIdentities,
    IReadOnlyList<TargetIdentity> Blockers);

internal static partial class TargetedProbeRunner
{
    private const string FailureKey = "ENGINEERING_TEST_EVIDENCE_FAILED";
    private const string Marker =
        "ENGINEERING_TEST_EVIDENCE_FAILED TRX is missing protected-base planned test identities count=";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static int ExtractBlockers(IReadOnlyList<string> arguments)
    {
        try
        {
            var options = StrictOptions.Parse(arguments, ["--log", "--output"]);
            var lines = File.ReadAllLines(options["--log"], StrictUtf8);
            var records = lines
                .Where(line => line.Contains(Marker, StringComparison.Ordinal))
                .Select(ParseFailureLine)
                .ToArray();
            if (records.Length == 0) return 1;
            if (records.Length != 1)
                throw new InvalidDataException("failure hint is duplicated");
            WriteJsonAtomically(
                options["--output"],
                new BlockerHintContract(1, records[0]));
            return 0;
        }
        catch (Exception exception) when (IsInputFailure(exception))
        {
            Console.Error.WriteLine("SELF_LOCK_TARGET_HINT_INVALID " + exception.GetType().Name);
            return 2;
        }
    }

    internal static int SelectTargets(IReadOnlyList<string> arguments)
    {
        try
        {
            var options = StrictOptions.Parse(
                arguments,
                ["--j1-repository", "--j0-repository", "--blockers", "--output"]);
            var j1 = ProcessTools.RequireRepositoryRoot(options["--j1-repository"]);
            var j0 = ProcessTools.RequireRepositoryRoot(options["--j0-repository"]);
            var blockers = Canonical(
                StrictArtifacts.ReadJson<BlockerHintContract>(options["--blockers"]).Blockers,
                "blockers");
            if (blockers.Length == 0)
                throw new InvalidDataException("blocker hint is empty");

            var j1Source = SourceIdentities(j1).ToHashSet(TargetIdentityComparer.Instance);
            var j0Source = SourceIdentities(j0).ToHashSet(TargetIdentityComparer.Instance);
            if (blockers.Any(blocker => !j1Source.Contains(blocker) || !j0Source.Contains(blocker)))
                throw new InvalidDataException("blocker is not owned by both subjects");

            var blockerSet = blockers.ToHashSet(TargetIdentityComparer.Instance);
            var sentinel = RunnableIdentities(j0)
                .FirstOrDefault(identity => !blockerSet.Contains(identity) && j1Source.Contains(identity))
                ?? throw new InvalidDataException("no common runnable sentinel identity exists");
            WriteJsonAtomically(
                options["--output"],
                new TargetSetContract(1, Canonical([.. blockers, sentinel], "required"), blockers));
            return 0;
        }
        catch (Exception exception) when (IsInputFailure(exception))
        {
            Console.Error.WriteLine("SELF_LOCK_TARGET_SELECTION_FAILED " + exception.GetType().Name);
            return 2;
        }
    }

    internal static int RunTargeted(IReadOnlyList<string> arguments)
    {
        try
        {
            var options = StrictOptions.Parse(
                arguments,
                [
                    "--repository", "--subject-kind", "--targets", "--staging-bundle",
                    "--evaluator-digest", "--dotnet",
                ],
                ["--j0-control"]);
            var repository = ProcessTools.RequireRepositoryRoot(options["--repository"]);
            var kind = options["--subject-kind"] switch
            {
                "merge" => SubjectKind.Merge,
                "synthetic_noop" => SubjectKind.SyntheticNoop,
                _ => throw new InvalidDataException("subject kind is unsupported"),
            };
            StrictArtifacts.EnsureDigest(options["--evaluator-digest"], "evaluator digest");
            var targets = StrictArtifacts.ReadJson<TargetSetContract>(options["--targets"]);
            if (targets.SchemaVersion != 1)
                throw new InvalidDataException("target set schema is unsupported");
            var required = Canonical(targets.RequiredIdentities, "required identities");
            var designatedBlockers = Canonical(targets.Blockers, "blockers");
            if (required.Length == 0
                || designatedBlockers.Length == 0
                || designatedBlockers.Except(required, TargetIdentityComparer.Instance).Any())
            {
                throw new InvalidDataException("target set is incomplete");
            }
            var control = options.GetValueOrDefault("--j0-control");
            if (kind == SubjectKind.SyntheticNoop)
            {
                if (control is null)
                    throw new InvalidDataException("synthetic no-op control is absent");
                J0ControlSeal.Validate(
                    repository,
                    options["--targets"],
                    options["--evaluator-digest"],
                    control);
            }
            else if (control is not null)
            {
                throw new InvalidDataException("merge subject cannot consume J0 control");
            }
            RunAndWriteEvidence(
                repository,
                kind,
                required,
                designatedBlockers,
                options["--staging-bundle"],
                options["--evaluator-digest"],
                options["--dotnet"]);
            if (control is not null)
            {
                J0ControlSeal.Validate(
                    repository,
                    options["--targets"],
                    options["--evaluator-digest"],
                    control);
            }
            return 0;
        }
        catch (Exception exception) when (IsInputFailure(exception))
        {
            Console.Error.WriteLine("SELF_LOCK_TARGET_EXECUTION_FAILED " + exception.GetType().Name);
            return 2;
        }
    }

    private static TargetIdentity[] ParseFailureLine(string line)
    {
        var markerIndex = line.IndexOf(Marker, StringComparison.Ordinal);
        var payload = line[(markerIndex + Marker.Length)..];
        var match = FailurePayload().Match(payload);
        if (!match.Success || !int.TryParse(match.Groups["count"].Value, out var count))
            throw new InvalidDataException("failure hint syntax is invalid");
        var identities = match.Groups["tests"].Value
            .Split(" | ", StringSplitOptions.None)
            .Select(ParseIdentity)
            .ToArray();
        var canonical = Canonical(identities, "failure hint");
        if (count != canonical.Length || !identities.SequenceEqual(canonical))
            throw new InvalidDataException("failure hint count or order is invalid");
        return canonical;
    }

    private static TargetIdentity ParseIdentity(string value)
    {
        var separator = value.IndexOf("::", StringComparison.Ordinal);
        if (separator <= 0 || separator != value.LastIndexOf("::", StringComparison.Ordinal))
            throw new InvalidDataException("failure identity syntax is invalid");
        return new TargetIdentity(value[..separator], value[(separator + 2)..]);
    }

    private static ImmutableArray<TargetIdentity> SourceIdentities(string repository) =>
        EngineeringTestPlanDeriver.DeriveSourceIdentities(Snapshot(repository))
            .Select(static identity => new TargetIdentity(identity.Assembly, identity.Id))
            .ToImmutableArray();

    private static IEnumerable<TargetIdentity> RunnableIdentities(string repository) =>
        EngineeringTestPlanDeriver.DeriveSnapshot(Snapshot(repository), [], full: true).Tests
            .Select(static test => new TargetIdentity(test.Assembly, test.Id))
            .Distinct()
            .OrderBy(static identity => identity.Assembly, StringComparer.Ordinal)
            .ThenBy(static identity => identity.TestId, StringComparer.Ordinal);

    private static RepositorySnapshot Snapshot(string repository) =>
        SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadRevision(repository, "HEAD")) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidDataException("subject snapshot is invalid: " + failure.Message),
            _ => throw new InvalidDataException("subject snapshot outcome is unknown"),
        };

    private static void RunAndWriteEvidence(
        string repository,
        SubjectKind kind,
        IReadOnlyList<TargetIdentity> required,
        IReadOnlyList<TargetIdentity> designatedBlockers,
        string stagingBundle,
        string evaluatorDigest,
        string dotnet)
    {
        var staging = Path.TrimEndingDirectorySeparator(Path.GetFullPath(stagingBundle));
        if (Directory.Exists(staging)) Directory.Delete(staging, recursive: true);
        var raw = Path.Combine(staging, "raw");
        Directory.CreateDirectory(raw);
        var filter = string.Join('|', required.Select(static identity =>
            "FullyQualifiedName~" + identity.TestId));
        var process = BoundedProcessRunner.Run(
            dotnet,
            [
                "test", "tools/StrataLint.sln", "--configuration", "Release",
                "--filter", filter,
                "--logger", "trx;LogFilePrefix=targeted",
                "--results-directory", raw,
            ],
            repository,
            BoundedProcessRunner.HangDetectionBudget,
            32 * 1024 * 1024);

        TestResultEvidence? evidence = null;
        try
        {
            evidence = TestResultEvidence.Load(raw);
        }
        catch (Exception) when (process.ExitCode != 0)
        {
        }
        var executed = evidence?.ExecutedTests
            .Select(static identity => new TargetIdentity(identity.Assembly, identity.Id))
            .ToHashSet(TargetIdentityComparer.Instance) ?? [];
        var observed = required
            .Where(executed.Contains)
            .Distinct(TargetIdentityComparer.Instance)
            .OrderBy(static identity => identity.Assembly, StringComparer.Ordinal)
            .ThenBy(static identity => identity.TestId, StringComparer.Ordinal)
            .ToArray();
        var missing = required.Except(observed, TargetIdentityComparer.Instance).ToArray();
        var semanticMissing = process.ExitCode == 0
            && missing.SequenceEqual(designatedBlockers, TargetIdentityComparer.Instance);
        var trx = WriteNormalizedTrx(staging, observed, required[0].Assembly);
        var subject = new SubjectContract(
            kind,
            ProcessTools.GitText(repository, "rev-parse", "HEAD"),
            ProcessTools.GitText(repository, "rev-parse", "HEAD^1"),
            ProcessTools.GitText(repository, "rev-parse", "HEAD^{tree}"),
            ProcessTools.GitText(repository, "rev-parse", "HEAD^1^{tree}"));
        var supervisor = new SupervisorFinalContract(
            1,
            "atomic",
            GateKind.Engineering,
            subject,
            evaluatorDigest,
            new TerminationContract(TerminationKind.Exited, process.ExitCode, null),
            DiagnosticsComplete: true,
            semanticMissing ? [FailureKey] : [],
            required.Select(static identity =>
                new IdentityContract(identity.Assembly, identity.TestId)).ToArray(),
            semanticMissing
                ? designatedBlockers.Select(static identity => new BlockerContract(
                    BlockerKind.MissingIdentity,
                    FailureKey,
                    identity.Assembly,
                    identity.TestId)).ToArray()
                : [],
            trx,
            [],
            process.ExitCode == 0 ? [] : ["targeted_dotnet_test_failed"]);
        WriteJsonAtomically(Path.Combine(staging, "supervisor-result.json"), supervisor);
        Directory.Delete(raw, recursive: true);
    }

    private static TrxArtifactContract[] WriteNormalizedTrx(
        string staging,
        IReadOnlyList<TargetIdentity> observed,
        string fallbackAssembly)
    {
        var root = Path.Combine(staging, "trx");
        Directory.CreateDirectory(root);
        var groups = observed
            .GroupBy(static identity => identity.Assembly)
            .Select(static group => (Assembly: group.Key, Identities: group.ToArray()))
            .ToList();
        if (groups.Count == 0) groups.Add((fallbackAssembly, []));
        var artifacts = new List<TrxArtifactContract>();
        for (var index = 0; index < groups.Count; index++)
        {
            var group = groups[index];
            var fileName = $"engineering-{index:D3}.trx";
            var path = Path.Combine(root, fileName);
            var document = new XDocument(
                new XElement("TestRun",
                    new XElement("Results", group.Identities.Select(identity => new XElement(
                        "UnitTestResult",
                        new XAttribute("testName", identity.TestId),
                        new XAttribute("outcome", "Passed")))),
                    new XElement("ResultSummary", new XElement(
                        "Counters",
                        new XAttribute("total", group.Identities.Length),
                        new XAttribute("executed", group.Identities.Length),
                        new XAttribute("passed", group.Identities.Length)))));
            File.WriteAllText(path, document.ToString(SaveOptions.DisableFormatting), StrictUtf8);
            artifacts.Add(new TrxArtifactContract(
                fileName,
                group.Assembly,
                StrictArtifacts.DigestFile(path)));
        }
        return artifacts.ToArray();
    }

    private static TargetIdentity[] Canonical(
        IEnumerable<TargetIdentity> identities,
        string field)
    {
        var result = identities
            .OrderBy(static identity => identity.Assembly, StringComparer.Ordinal)
            .ThenBy(static identity => identity.TestId, StringComparer.Ordinal)
            .ToArray();
        foreach (var identity in result)
        {
            StrictArtifacts.EnsureSafeIdentity(identity.Assembly, field + " assembly");
            StrictArtifacts.EnsureSafeIdentity(identity.TestId, field + " test id");
            if (!IdentityPart().IsMatch(identity.Assembly)
                || !IdentityPart().IsMatch(identity.TestId))
                throw new InvalidDataException(field + " identity is not canonical");
        }
        if (result.Distinct(TargetIdentityComparer.Instance).Count() != result.Length)
            throw new InvalidDataException(field + " identities are duplicated");
        return result;
    }

    private static void WriteJsonAtomically<T>(string path, T value)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
        var temporary = path + ".tmp-" + Environment.ProcessId;
        File.WriteAllBytes(temporary, JsonSerializer.SerializeToUtf8Bytes(value, ContractJson.Options));
        File.Move(temporary, path, overwrite: true);
    }

    private static bool IsInputFailure(Exception exception) => exception is
        IOException or UnauthorizedAccessException or InvalidDataException or JsonException
        or ArgumentException or InvalidOperationException;

    [GeneratedRegex(
        "\\A(?<count>[1-9][0-9]*) tests=(?<tests>[^\\r\\n]+)\\z",
        RegexOptions.CultureInvariant)]
    private static partial Regex FailurePayload();

    [GeneratedRegex("\\A[A-Za-z0-9_.+`-]+\\z", RegexOptions.CultureInvariant)]
    private static partial Regex IdentityPart();
}

internal sealed class StrictOptions : Dictionary<string, string>
{
    private StrictOptions() : base(StringComparer.Ordinal) { }

    internal static StrictOptions Parse(
        IReadOnlyList<string> arguments,
        IReadOnlyList<string> expected,
        IReadOnlyList<string>? optional = null)
    {
        optional ??= [];
        var result = new StrictOptions();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count
                || (!expected.Contains(arguments[index]) && !optional.Contains(arguments[index]))
                || string.IsNullOrWhiteSpace(arguments[index + 1])
                || !result.TryAdd(arguments[index], arguments[index + 1]))
            {
                throw new ArgumentException("options are invalid");
            }
        }
        if (expected.Any(name => !result.ContainsKey(name))
            || result.Count > expected.Count + optional.Count)
            throw new ArgumentException("options are incomplete");
        return result;
    }
}

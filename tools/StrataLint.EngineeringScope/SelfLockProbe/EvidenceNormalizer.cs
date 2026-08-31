using System.Globalization;
using System.Text.Json;
using System.Xml;
using System.Xml.Linq;

namespace StrataLint.EngineeringScope.SelfLockProbe;

internal static class EvidenceNormalizer
{
    private const string RegisteredFailureKey = "ENGINEERING_TEST_EVIDENCE_FAILED";

    internal static NormalizedJudgment Normalize(
        string label,
        SubjectKind expectedKind,
        string repository,
        string bundle,
        string evaluatorDigest,
        string controllerRoot)
    {
        try
        {
            return NormalizeCore(
                label,
                expectedKind,
                repository,
                bundle,
                evaluatorDigest,
                controllerRoot);
        }
        catch (Exception exception) when (exception is
            IOException or UnauthorizedAccessException or InvalidDataException
            or JsonException or XmlException or FormatException)
        {
            return NormalizedJudgment.Infrastructure(
                GateKind.Engineering,
                label,
                "evidence_invalid:" + exception.GetType().Name);
        }
    }

    private static NormalizedJudgment NormalizeCore(
        string label,
        SubjectKind expectedKind,
        string repository,
        string bundle,
        string evaluatorDigest,
        string controllerRoot)
    {
        var physicalRepository = ProcessTools.RequireRepositoryRoot(repository);
        var physicalBundle = Path.GetFullPath(bundle);
        if (!Directory.Exists(physicalBundle)
            || IsWithin(physicalBundle, physicalRepository))
        {
            throw new InvalidDataException("evidence bundle is absent or candidate-owned");
        }

        var payload = AuthorizedPayload(controllerRoot, physicalBundle);
        var supervisorPath = Path.Combine(payload, "supervisor-result.json");
        var sentinelPath = Path.Combine(payload, "finalization.sentinel");
        var sentinel = StrictArtifacts.ReadJson<FinalizationSentinelContract>(sentinelPath);
        if (sentinel.SchemaVersion != 1)
        {
            throw new InvalidDataException("unsupported sentinel schema");
        }
        StrictArtifacts.EnsureDigest(
            sentinel.SupervisorResultSha256,
            "supervisor_result_sha256");
        if (sentinel.SupervisorResultSha256 != StrictArtifacts.DigestFile(supervisorPath))
        {
            throw new InvalidDataException("supervisor result is not sentinel-bound");
        }

        var supervisor = StrictArtifacts.ReadJson<SupervisorFinalContract>(supervisorPath);
        ValidateSupervisor(supervisor, expectedKind, evaluatorDigest);
        ValidateSubject(physicalRepository, supervisor.Subject, expectedKind);
        var observed = ReadTrx(
            payload,
            supervisor.TrxArtifacts,
            sentinel.TrxArtifacts);
        var required = CanonicalIdentities(supervisor.RequiredIdentities, "required identities");
        var blockers = CanonicalBlockers(supervisor.Blockers);
        var missing = required.Except(observed).ToArray();
        var blockerIdentities = blockers
            .Select(static blocker => new IdentityContract(blocker.Assembly, blocker.TestId))
            .ToArray();
        var coverageComplete = missing.SequenceEqual(blockerIdentities);
        var coverage = new CoverageContract(coverageComplete, required, observed);

        if (supervisor.Termination.Kind != TerminationKind.Exited
            || supervisor.Termination.ExitCode is null
            || supervisor.Termination.Signal is not null)
        {
            return Infrastructure(
                supervisor,
                label,
                coverage,
                IsObservedRunnerShutdown(supervisor, blockers, missing)
                    ? "runner_shutdown_observed"
                    : "child_not_normally_terminated");
        }
        if (!supervisor.DiagnosticsComplete)
        {
            return Infrastructure(supervisor, label, coverage, "diagnostics_incomplete");
        }

        if (supervisor.FailureKeys.Count == 0)
        {
            var admitted = supervisor.Termination.ExitCode == 0
                && blockers.Length == 0
                && missing.Length == 0;
            return admitted
                ? Judgment(supervisor, label, JudgmentOutcome.Admit, coverage, [])
                : Infrastructure(supervisor, label, coverage, "policy_artifact_absent");
        }

        var registeredFailure = supervisor.FailureKeys.Count == 1
            && supervisor.FailureKeys[0] == RegisteredFailureKey
            && blockers.Length != 0
            && blockers.All(static blocker =>
                blocker.Kind == BlockerKind.MissingIdentity
                && blocker.FailureKey == RegisteredFailureKey)
            && coverageComplete;
        return registeredFailure
            ? Judgment(supervisor, label, JudgmentOutcome.SemanticReject, coverage, [])
            : Infrastructure(supervisor, label, coverage, "unregistered_or_incomplete_policy_failure");
    }

    private static bool IsObservedRunnerShutdown(
        SupervisorFinalContract supervisor,
        IReadOnlyList<BlockerContract> blockers,
        IReadOnlyList<IdentityContract> missing)
    {
        if (!supervisor.DiagnosticsComplete
            || supervisor.FailureKeys.Count != 0
            || blockers.Count != 0
            || missing.Count != 0
            || supervisor.StepFailures.Count != 0
            || supervisor.Diagnostics.Count != 1
            || supervisor.Termination.ExitCode is not null)
        {
            return false;
        }
        var diagnostic = supervisor.Diagnostics[0];
        return supervisor.Termination is { Kind: TerminationKind.Signal, Signal: "SIGTERM" }
                && diagnostic == "MSBUILD : error MSB4166: Child node \"N\" exited prematurely. Shutting down.\nmake: *** [Makefile:23: engineering-tests] Error 143"
            || supervisor.Termination is { Kind: TerminationKind.Cancellation, Signal: null }
                && diagnostic is "##[error]The runner has received a shutdown signal."
                    or "##[error]The operation was canceled.";
    }

    private static string AuthorizedPayload(string controllerRoot, string bundle)
    {
        var pointer = StrictArtifacts.ReadJson<PublicationPointerContract>(
            Path.Combine(bundle, "publication.json"));
        if (pointer.SchemaVersion != 1
            || pointer.PublicationId.Length != 64
            || pointer.PublicationId.Any(static character =>
                character is not (>= '0' and <= '9') and not (>= 'a' and <= 'f'))
            || pointer.PayloadDirectory != "payloads/" + pointer.PublicationId)
        {
            throw new InvalidDataException("publication pointer is invalid");
        }
        StrictArtifacts.EnsureDigest(pointer.SentinelSha256, "publication sentinel_sha256");
        var payload = Path.GetFullPath(Path.Combine(bundle, pointer.PayloadDirectory));
        if (!Directory.Exists(payload)
            || !IsWithin(payload, bundle)
            || (File.GetAttributes(payload) & FileAttributes.ReparsePoint) != 0)
        {
            throw new InvalidDataException("publication payload is absent or linked");
        }
        var sentinelPath = Path.Combine(payload, "finalization.sentinel");
        if (StrictArtifacts.DigestFile(sentinelPath) != pointer.SentinelSha256)
            throw new InvalidDataException("publication pointer does not bind its sentinel");

        var receipt = StrictArtifacts.ReadJson<AuthorityReceiptContract>(
            StrictArtifacts.AuthorityReceiptPath(controllerRoot, bundle));
        var closure = ControllerClosure.Derive(controllerRoot);
        var producerDigest = StrictArtifacts.ProducerDigest(controllerRoot);
        var supervisorDigest = StrictArtifacts.DigestFile(
            Path.Combine(payload, "supervisor-result.json"));
        var sentinel = StrictArtifacts.ReadJson<FinalizationSentinelContract>(sentinelPath);
        if (receipt.SchemaVersion != 1
            || receipt.ControllerCommit != closure.Commit
            || receipt.ProducerPath != ControllerClosure.ProducerPath
            || receipt.ProducerSha256 != producerDigest
            || receipt.BundlePath != bundle
            || receipt.PublicationId != pointer.PublicationId
            || receipt.PayloadDirectory != pointer.PayloadDirectory
            || receipt.SentinelSha256 != pointer.SentinelSha256
            || receipt.SupervisorResultSha256 != supervisorDigest
            || receipt.TrxArtifacts is null
            || sentinel.TrxArtifacts is null
            || !receipt.TrxArtifacts.SequenceEqual(sentinel.TrxArtifacts))
        {
            throw new InvalidDataException("publication authority receipt is invalid");
        }
        return payload;
    }

    private static void ValidateSupervisor(
        SupervisorFinalContract supervisor,
        SubjectKind expectedKind,
        string evaluatorDigest)
    {
        if (supervisor.SchemaVersion != 1
            || supervisor.Publication != "atomic"
            || supervisor.Gate != GateKind.Engineering
            || supervisor.Subject is null
            || supervisor.Subject.Kind != expectedKind)
        {
            throw new InvalidDataException("supervisor contract header is invalid");
        }
        StrictArtifacts.EnsureDigest(supervisor.EvaluatorDigest, "evaluator_digest");
        if (supervisor.EvaluatorDigest != evaluatorDigest)
        {
            throw new InvalidDataException("evaluator digest differs from the base controller");
        }
        if (supervisor.FailureKeys is null
            || supervisor.RequiredIdentities is null
            || supervisor.Blockers is null
            || supervisor.TrxArtifacts is null
            || supervisor.Diagnostics is null
            || supervisor.StepFailures is null
            || supervisor.Termination is null)
        {
            throw new InvalidDataException("supervisor contract has a missing collection");
        }
        if (supervisor.FailureKeys.Any(static key => string.IsNullOrEmpty(key))
            || supervisor.FailureKeys.Distinct(StringComparer.Ordinal).Count()
                != supervisor.FailureKeys.Count)
        {
            throw new InvalidDataException("failure keys are invalid or duplicated");
        }
    }

    private static void ValidateSubject(
        string repository,
        SubjectContract subject,
        SubjectKind expectedKind)
    {
        StrictArtifacts.EnsureObjectId(subject.HeadSha, "subject.head_sha");
        StrictArtifacts.EnsureObjectId(subject.BaseSha, "subject.base_sha");
        StrictArtifacts.EnsureObjectId(subject.HeadTreeSha, "subject.head_tree_sha");
        StrictArtifacts.EnsureObjectId(subject.BaseTreeSha, "subject.base_tree_sha");
        var actualHead = ProcessTools.GitText(repository, "rev-parse", "HEAD");
        var actualBase = ProcessTools.GitText(repository, "rev-parse", "HEAD^1");
        var actualHeadTree = ProcessTools.GitText(repository, "rev-parse", "HEAD^{tree}");
        var actualBaseTree = ProcessTools.GitText(repository, "rev-parse", "HEAD^1^{tree}");
        if (subject.HeadSha != actualHead
            || subject.BaseSha != actualBase
            || subject.HeadTreeSha != actualHeadTree
            || subject.BaseTreeSha != actualBaseTree)
        {
            throw new InvalidDataException("subject is not bound to checked HEAD and HEAD^1");
        }
        if (expectedKind == SubjectKind.SyntheticNoop
            && actualHeadTree != actualBaseTree)
        {
            throw new InvalidDataException("synthetic no-op changes its base tree");
        }
        if (expectedKind == SubjectKind.Merge)
        {
            var parentRecord = ProcessTools.GitText(repository, "rev-list", "--parents", "-n", "1", "HEAD");
            if (parentRecord.Split(' ', StringSplitOptions.RemoveEmptyEntries).Length < 3)
            {
                throw new InvalidDataException("J1 subject is not a merge");
            }
        }
    }

    private static IdentityContract[] ReadTrx(
        string bundle,
        IReadOnlyList<TrxArtifactContract> artifacts,
        IReadOnlyList<SentinelTrxContract> sentinelArtifacts)
    {
        if (artifacts.Count == 0 || sentinelArtifacts.Count != artifacts.Count)
        {
            throw new InvalidDataException("TRX manifest is empty or incomplete");
        }
        var sentinelByName = sentinelArtifacts.ToDictionary(
            static item => item.FileName,
            StringComparer.Ordinal);
        var observed = new List<IdentityContract>();
        var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var artifact in artifacts.OrderBy(static item => item.FileName, StringComparer.Ordinal))
        {
            ValidateArtifactName(artifact.FileName);
            StrictArtifacts.EnsureSafeIdentity(artifact.Assembly, "trx assembly");
            StrictArtifacts.EnsureDigest(artifact.Sha256, "trx sha256");
            if (!names.Add(artifact.FileName)
                || !sentinelByName.TryGetValue(artifact.FileName, out var sentinel)
                || sentinel.Sha256 != artifact.Sha256)
            {
                throw new InvalidDataException("TRX manifest is duplicated or not sentinel-bound");
            }
            var path = Path.Combine(bundle, "trx", artifact.FileName);
            if (StrictArtifacts.DigestFile(path) != artifact.Sha256)
            {
                throw new InvalidDataException("TRX digest differs from its manifest");
            }
            observed.AddRange(ReadTrxFile(path, artifact.Assembly));
        }
        return CanonicalIdentities(observed, "observed identities");
    }

    private static IReadOnlyList<IdentityContract> ReadTrxFile(string path, string assembly)
    {
        using var stream = File.OpenRead(path);
        using var reader = XmlReader.Create(stream, new XmlReaderSettings
        {
            DtdProcessing = DtdProcessing.Prohibit,
            XmlResolver = null,
        });
        var document = XDocument.Load(reader, LoadOptions.None);
        var results = document.Descendants()
            .Where(static element => element.Name.LocalName == "UnitTestResult")
            .Select(element => new
            {
                Name = RequiredAttribute(element, "testName"),
                Outcome = RequiredAttribute(element, "outcome"),
            })
            .ToArray();
        var counters = document.Descendants()
            .SingleOrDefault(static element => element.Name.LocalName == "Counters")
            ?? throw new InvalidDataException("TRX counters are absent or duplicated");
        var total = Counter(counters, "total");
        var executed = Counter(counters, "executed");
        var passed = Counter(counters, "passed");
        if (total != results.Length
            || executed != results.Length
            || executed == 0
            || passed != results.Length
            || results.Any(static result => result.Outcome != "Passed"))
        {
            throw new InvalidDataException("TRX is partial, zero-execution, or non-passing");
        }
        return results.Select(result =>
        {
            StrictArtifacts.EnsureSafeIdentity(result.Name, "TRX test name");
            return new IdentityContract(assembly, result.Name);
        }).ToArray();
    }

    private static IdentityContract[] CanonicalIdentities(
        IEnumerable<IdentityContract> identities,
        string field)
    {
        var canonical = identities.OrderBy(static identity => identity.Assembly, StringComparer.Ordinal)
            .ThenBy(static identity => identity.TestId, StringComparer.Ordinal)
            .ToArray();
        foreach (var identity in canonical)
        {
            StrictArtifacts.EnsureSafeIdentity(identity.Assembly, field + " assembly");
            StrictArtifacts.EnsureSafeIdentity(identity.TestId, field + " test_id");
        }
        if (canonical.Distinct().Count() != canonical.Length)
        {
            throw new InvalidDataException(field + " contain duplicates");
        }
        return canonical;
    }

    private static BlockerContract[] CanonicalBlockers(IEnumerable<BlockerContract> blockers)
    {
        var canonical = blockers.OrderBy(static blocker => blocker.Assembly, StringComparer.Ordinal)
            .ThenBy(static blocker => blocker.TestId, StringComparer.Ordinal)
            .ToArray();
        foreach (var blocker in canonical)
        {
            StrictArtifacts.EnsureSafeIdentity(blocker.Assembly, "blocker assembly");
            StrictArtifacts.EnsureSafeIdentity(blocker.TestId, "blocker test_id");
        }
        if (canonical.Distinct().Count() != canonical.Length)
        {
            throw new InvalidDataException("blockers contain duplicates");
        }
        return canonical;
    }

    private static NormalizedJudgment Infrastructure(
        SupervisorFinalContract supervisor,
        string label,
        CoverageContract coverage,
        string reason) => Judgment(
            supervisor,
            label,
            JudgmentOutcome.InfrastructureFailure,
            coverage,
            [reason]);

    private static NormalizedJudgment Judgment(
        SupervisorFinalContract supervisor,
        string label,
        string outcome,
        CoverageContract coverage,
        IReadOnlyList<string> reasons) => new(
            supervisor.Gate,
            label,
            outcome,
            supervisor.EvaluatorDigest,
            supervisor.Subject,
            supervisor.FailureKeys,
            supervisor.Blockers,
            coverage,
            reasons);

    private static string RequiredAttribute(XElement element, string name) =>
        element.Attribute(name)?.Value
        ?? throw new InvalidDataException($"TRX {name} attribute is absent");

    private static int Counter(XElement counters, string name) =>
        int.Parse(RequiredAttribute(counters, name), NumberStyles.None, CultureInfo.InvariantCulture);

    private static void ValidateArtifactName(string name)
    {
        if (string.IsNullOrEmpty(name)
            || name != Path.GetFileName(name)
            || !name.EndsWith(".trx", StringComparison.Ordinal)
            || name.Any(static character => char.IsControl(character) || character is '/' or '\\'))
        {
            throw new InvalidDataException("TRX file name is not canonical");
        }
    }

    private static bool IsWithin(string path, string parent)
    {
        var relative = Path.GetRelativePath(parent, path);
        return relative != ".."
            && !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal)
            && !Path.IsPathRooted(relative);
    }
}

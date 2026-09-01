using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.EngineeringScope;

internal sealed record PureRevertConclusion(
    string State,
    string CandidateBaseSha,
    string CandidateHeadSha,
    string TargetMergeSha,
    string Reason);

internal static partial class ProbeReducer
{
    private const string PureTrue = "true";
    private const string PureFalse = "false";
    private const string PureIndeterminate = "indeterminate";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static (ProbeResultContract Result, int ExitCode) Evaluate(ProbeOptions options)
    {
        var candidate = ProcessTools.RequireRepositoryRoot(options.CandidateRepository);
        var candidateHead = ProcessTools.GitText(candidate, "rev-parse", "HEAD");
        var candidateBase = ProcessTools.GitText(candidate, "rev-parse", "HEAD^1");
        var pure = RunPureRevert(options.PureRevertScript, candidate, candidateHead, candidateBase);
        if (pure.State == PureIndeterminate)
        {
            return Decision(
                "PROBE_INDETERMINATE",
                false,
                candidateHead,
                string.Empty,
                [pure.Reason],
                [],
                2);
        }
        if (pure.State == PureFalse)
        {
            return Decision(
                "TRUE_RED_CONFIRMED",
                false,
                candidateHead,
                string.Empty,
                [pure.Reason],
                [],
                1);
        }
        if (!OwnerClosureUnchanged(options.ControllerRoot, candidate, out var ownerReason))
        {
            return Decision(
                "TRUE_RED_CONFIRMED",
                false,
                candidateHead,
                pure.TargetMergeSha,
                [ownerReason],
                [],
                1);
        }
        if (options.RedGates.Count == 0)
        {
            return Decision(
                "TRUE_RED_CONFIRMED",
                false,
                candidateHead,
                pure.TargetMergeSha,
                ["red_gate_set_empty"],
                [],
                1);
        }
        if (options.RequiredGates.Any(static gate => gate != GateKind.Engineering)
            || options.RedGates.Any(static gate => gate != GateKind.Engineering))
        {
            return Decision(
                "PROBE_INDETERMINATE",
                false,
                candidateHead,
                pure.TargetMergeSha,
                ["unsupported_gate_handler"],
                [],
                2);
        }

        var evaluatorDigest = StrictArtifacts.EvaluatorDigest(options.ControllerRoot);
        var j1 = EvidenceNormalizer.Normalize(
            "j1",
            SubjectKind.Merge,
            options.J1Repository,
            options.J1Bundle,
            evaluatorDigest,
            options.ControllerRoot);
        var j0 = EvidenceNormalizer.Normalize(
            "j0",
            SubjectKind.SyntheticNoop,
            options.J0Repository,
            options.J0Bundle,
            evaluatorDigest,
            options.ControllerRoot);
        var judgments = new[] { j1, j0 };
        if (judgments.Any(static judgment =>
                judgment.Outcome is JudgmentOutcome.InfrastructureFailure or JudgmentOutcome.Unsupported))
        {
            return Decision(
                "PROBE_INDETERMINATE",
                false,
                candidateHead,
                pure.TargetMergeSha,
                judgments.SelectMany(static judgment => judgment.ReasonCodes).DefaultIfEmpty("evidence_incomplete").ToArray(),
                judgments,
                2);
        }
        if (!SubjectsBind(pure, j1, j0))
        {
            return Decision(
                "PROBE_INDETERMINATE",
                false,
                candidateHead,
                pure.TargetMergeSha,
                ["subject_binding_mismatch"],
                judgments,
                2);
        }

        var engineeringSatisfied = j1.Outcome == JudgmentOutcome.Admit
            || (options.RedGates.Contains(GateKind.Engineering)
                && j1.Outcome == JudgmentOutcome.SemanticReject
                && j0.Outcome == JudgmentOutcome.SemanticReject
                && CoverageComplete(j1, j0)
                && J1BlockersOwnedByBase(j1, j0));
        if (!engineeringSatisfied)
        {
            return Decision(
                "TRUE_RED_CONFIRMED",
                false,
                candidateHead,
                pure.TargetMergeSha,
                ["gate_predicate_not_satisfied"],
                judgments,
                1);
        }

        return Decision(
            "SELF_LOCK_CONFIRMED",
            true,
            candidateHead,
            pure.TargetMergeSha,
            ["exact_revert_and_registered_self_lock_confirmed"],
            judgments,
            0,
            ["engineering"]);
    }

    private static PureRevertConclusion RunPureRevert(
        string script,
        string candidate,
        string expectedHead,
        string expectedBase)
    {
        var output = ProcessTools.Run("/bin/bash", [script, candidate], candidate);
        try
        {
            var stdout = StrictUtf8.GetString(output.StandardOutput);
            var stderr = StrictUtf8.GetString(output.StandardError);
            if (output.ExitCode == 0)
            {
                if (stderr.Length != 0)
                {
                    return Indeterminate("pure_revert_conclusion_parse_failed");
                }
                var match = PureRevertTrueRegex().Match(stdout);
                if (!match.Success
                    || match.Groups["head"].Value != expectedHead
                    || match.Groups["base"].Value != expectedBase)
                {
                    return Indeterminate("pure_revert_conclusion_parse_failed");
                }
                return new PureRevertConclusion(
                    PureTrue,
                    expectedBase,
                    expectedHead,
                    match.Groups["target"].Value,
                    "pure_revert_true");
            }

            var logicalConclusions = new Dictionary<int, (string Marker, string Reason)>
            {
                [4] = ("PURE_REVERT_NO_CHANGES", "pure_revert_no_changes"),
                [5] = ("PURE_REVERT_NOT_INVERSE", "pure_revert_not_inverse"),
                [6] = ("PURE_REVERT_PATH_OUTSIDE_ALLOWLIST", "pure_revert_path_outside_allowlist"),
                [7] = ("PURE_REVERT_AMBIGUOUS_TARGET", "pure_revert_ambiguous_target"),
                [8] = ("PURE_REVERT_SECOND_PARENT", "pure_revert_second_parent"),
                [9] = ("PURE_REVERT_CLASSIFIER_MODIFIED", "pure_revert_classifier_modified"),
                [11] = ("PURE_REVERT_TARGET_NOT_A_MERGE", "pure_revert_target_not_merge"),
            };
            if (logicalConclusions.TryGetValue(output.ExitCode, out var conclusion)
                && stdout.Length == 0
                && stderr == conclusion.Marker + "\n")
            {
                return new PureRevertConclusion(
                    PureFalse,
                    expectedBase,
                    expectedHead,
                    string.Empty,
                    conclusion.Reason);
            }
        }
        catch (DecoderFallbackException)
        {
            return Indeterminate("pure_revert_conclusion_parse_failed");
        }
        return Indeterminate("pure_revert_conclusion_parse_failed");
    }

    private static bool OwnerClosureUnchanged(
        string controllerRoot,
        string candidate,
        out string reason)
    {
        var ownerPaths = ControllerClosure.Derive(controllerRoot).OwnerPaths;
        var output = ProcessTools.Run(
            "/usr/bin/git",
            ["-C", candidate, "diff-tree", "-r", "--no-commit-id", "--name-only", "-z", "HEAD^1", "HEAD"],
            candidate);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
        {
            throw new InvalidDataException("candidate path enumeration failed");
        }
        foreach (var bytes in SplitNul(output.StandardOutput))
        {
            string path;
            try
            {
                path = StrictUtf8.GetString(bytes);
            }
            catch (DecoderFallbackException)
            {
                reason = "candidate_path_invalid";
                return false;
            }
            if (!IsCanonicalPath(path) || ownerPaths.Contains(path))
            {
                reason = IsCanonicalPath(path)
                    ? "probe_owner_closure_changed"
                    : "candidate_path_invalid";
                return false;
            }
        }
        reason = string.Empty;
        return true;
    }

    private static bool SubjectsBind(
        PureRevertConclusion pure,
        NormalizedJudgment j1,
        NormalizedJudgment j0) =>
        j1.SubjectContract is { } j1Subject
        && j0.SubjectContract is { } j0Subject
        && j1Subject.HeadSha == pure.TargetMergeSha
        && j1Subject.BaseSha == j0Subject.BaseSha
        && j0Subject.HeadTreeSha == j0Subject.BaseTreeSha
        && j1.EvaluatorDigest == j0.EvaluatorDigest;

    private static bool CoverageComplete(
        NormalizedJudgment j1,
        NormalizedJudgment j0) =>
        j1.Coverage is { Complete: true } j1Coverage
        && j0.Coverage is { Complete: true } j0Coverage
        && j1Coverage.RequiredIdentities.SequenceEqual(j0Coverage.RequiredIdentities)
        && j1Coverage.ObservedIdentities.SequenceEqual(j0Coverage.ObservedIdentities);

    private static bool J1BlockersOwnedByBase(
        NormalizedJudgment j1,
        NormalizedJudgment j0) =>
        j1.Blockers.All(blocker => j0.Blockers.Contains(blocker));

    private static (ProbeResultContract Result, int ExitCode) Decision(
        string decision,
        bool allow,
        string candidateHead,
        string targetMerge,
        IReadOnlyList<string> reasons,
        IReadOnlyList<NormalizedJudgment> judgments,
        int exitCode,
        IReadOnlyList<string>? confirmedRedGates = null) =>
        (new ProbeResultContract(
            1,
            decision,
            new AuthorizationContract(
                allow,
                ChangesGateStatus: false,
                RerunRequiredAfterDevPush: true,
                confirmedRedGates ?? [],
                candidateHead,
                targetMerge),
            reasons.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray(),
            judgments), exitCode);

    private static PureRevertConclusion Indeterminate(string reason) =>
        new(PureIndeterminate, string.Empty, string.Empty, string.Empty, reason);

    private static IEnumerable<byte[]> SplitNul(byte[] bytes)
    {
        if (bytes.Length == 0)
        {
            yield break;
        }
        if (bytes[^1] != 0)
        {
            throw new InvalidDataException("candidate path record is partial");
        }
        var start = 0;
        for (var index = 0; index < bytes.Length; index++)
        {
            if (bytes[index] != 0) continue;
            if (index == start)
            {
                throw new InvalidDataException("candidate path record is empty");
            }
            yield return bytes[start..index];
            start = index + 1;
        }
    }

    private static bool IsCanonicalPath(string path) =>
        path.Length != 0
        && !path.StartsWith("/", StringComparison.Ordinal)
        && !path.Contains('\\', StringComparison.Ordinal)
        && !path.Any(static character => char.IsControl(character) || char.IsSurrogate(character))
        && path.Split('/').All(static segment => segment.Length != 0 && segment is not "." and not "..");

    [GeneratedRegex(
        "\\APURE_REVERT_TRUE base_sha=(?<base>[0-9a-f]{40}|[0-9a-f]{64}) head_sha=(?<head>[0-9a-f]{40}|[0-9a-f]{64}) target_merge_sha=(?<target>[0-9a-f]{40}|[0-9a-f]{64}) changed_path_count=[1-9][0-9]*\\n\\z",
        RegexOptions.CultureInvariant)]
    private static partial Regex PureRevertTrueRegex();
}

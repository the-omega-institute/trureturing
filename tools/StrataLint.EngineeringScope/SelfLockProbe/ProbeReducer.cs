using System.Text;

namespace StrataLint.EngineeringScope;

internal static class ProbeReducer
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static (ProbeResultContract Result, int ExitCode) Evaluate(ProbeOptions options)
    {
        var candidate = ProcessTools.RequireRepositoryRoot(options.CandidateRepository);
        var candidateHead = ProcessTools.GitText(candidate, "rev-parse", "HEAD");
        var candidateBase = ProcessTools.GitText(candidate, "rev-parse", "HEAD^1");
        if (!OwnerClosureUnchanged(options.ControllerRoot, candidate, out var ownerReason))
        {
            return Decision(
                "TRUE_RED_CONFIRMED",
                candidateHead,
                candidateBase,
                [ownerReason],
                [],
                1);
        }
        if (options.RedGates.Count == 0)
        {
            return Decision(
                "TRUE_RED_CONFIRMED",
                candidateHead,
                candidateBase,
                ["red_gate_set_empty"],
                [],
                1);
        }
        if (options.RequiredGates.Any(static gate => gate != GateKind.Engineering)
            || options.RedGates.Any(static gate => gate != GateKind.Engineering))
        {
            return Decision(
                "PROBE_INDETERMINATE",
                candidateHead,
                candidateBase,
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
                candidateHead,
                candidateBase,
                judgments.SelectMany(static judgment => judgment.ReasonCodes).DefaultIfEmpty("evidence_incomplete").ToArray(),
                judgments,
                2);
        }
        if (!SubjectsBind(candidateBase, j1, j0))
        {
            return Decision(
                "PROBE_INDETERMINATE",
                candidateHead,
                candidateBase,
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
                candidateHead,
                candidateBase,
                ["gate_predicate_not_satisfied"],
                judgments,
                1);
        }

        return Decision(
            "SELF_LOCK_CONFIRMED",
            candidateHead,
            candidateBase,
            ["registered_self_lock_confirmed"],
            judgments,
            0,
            ["engineering"]);
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
        string candidateBase,
        NormalizedJudgment j1,
        NormalizedJudgment j0) =>
        j1.SubjectContract is { } j1Subject
        && j0.SubjectContract is { } j0Subject
        && j1Subject.HeadSha == candidateBase
        && j1Subject.BaseSha == j0Subject.BaseSha
        && j0Subject.HeadTreeSha == j0Subject.BaseTreeSha
        && j1.EvaluatorDigest == j0.EvaluatorDigest;

    private static bool CoverageComplete(
        NormalizedJudgment j1,
        NormalizedJudgment j0) =>
        j1.Coverage is { Complete: true } j1Coverage
        && j0.Coverage is { Complete: true } j0Coverage
        && j1Coverage.ObservedIdentities.SequenceEqual(j0Coverage.ObservedIdentities);

    private static bool J1BlockersOwnedByBase(
        NormalizedJudgment j1,
        NormalizedJudgment j0) =>
        j1.Blockers.All(blocker => j0.Blockers.Contains(blocker));

    private static (ProbeResultContract Result, int ExitCode) Decision(
        string decision,
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
                ChangesGateStatus: false,
                RerunRequiredAfterDevPush: true,
                confirmedRedGates ?? [],
                candidateHead,
                targetMerge),
            reasons.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray(),
            judgments), exitCode);

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

}

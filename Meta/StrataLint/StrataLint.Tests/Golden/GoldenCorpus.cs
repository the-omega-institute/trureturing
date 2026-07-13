using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed record GoldenCase(
    string Name,
    IReadOnlyList<GoldenMutation> BaselineMutations,
    IReadOnlyList<GoldenMutation> Mutations,
    IReadOnlyList<GoldenDiagnostic> ExpectedDiagnostics);

internal sealed record GoldenDiagnostic(RuleId RuleId, RepoPath Path, string Message)
{
    internal string Render() => $"{RuleId.Value} {Path.Value}: {Message}";
}

internal abstract record GoldenMutation
{
    internal sealed record Write(RepoPath Path, string Content) : GoldenMutation;

    internal sealed record WriteParts(RepoPath Path, IReadOnlyList<string> Parts) : GoldenMutation;

    internal sealed record Lean(
        RepoPath Path,
        string RawGid,
        Generality Generality,
        string Body) : GoldenMutation;

    internal sealed record Delete(RepoPath Path) : GoldenMutation;

    internal sealed record AppendLines(RepoPath Path, int Count, string Line) : GoldenMutation;

    internal sealed record AddDomain(DomainId Name, Stratum Stratum) : GoldenMutation;

    internal sealed record AddTask(RepoPath Path, string RawGid, string RawCaseId) : GoldenMutation;

    internal sealed record PopulateDirectory : GoldenMutation;

    internal sealed record EmptyMirrorWaiver : GoldenMutation;

    internal sealed record EvidenceMirror(bool IncludeJson, bool IncludeYaml) : GoldenMutation;

    internal sealed record ReplaceBackfill(string OldValue, string NewValue) : GoldenMutation;

    internal sealed record ReplaceFirstBackfillDisposition(string RawGid) : GoldenMutation;

    internal sealed record MutateBackfillAnchor(string Anchor, bool Duplicate) : GoldenMutation;
}

internal static partial class GoldenCorpus
{
    private const string RingPath = RuleFixture.RingPath;
    private const string BlueprintPath = RuleFixture.BlueprintPath;
    private const string NotationPath = RuleFixture.NotationPath;
    private const string AssumptionDebtPath = RuleFixture.AssumptionDebtPath;
    private const string HeartsPath = RuleFixture.HeartsPath;

    internal static IReadOnlyList<GoldenCase> All { get; } =
    [
        .. Corpus1,
        .. Corpus2,
        .. Corpus3,
        .. Corpus4,
    ];

    private static GoldenCase C(
        string name,
        GoldenMutation[] baselineMutations,
        GoldenMutation[] mutations,
        GoldenDiagnostic[] expectedDiagnostics) =>
        new(name, baselineMutations, mutations, expectedDiagnostics);

    private static GoldenDiagnostic D(int rule, string path, string message) =>
        new(RuleId.CreateKnown(rule), P(path), message);

    private static GoldenMutation W(string path, string content) =>
        new GoldenMutation.Write(P(path), content);

    private static GoldenMutation WP(string path, params string[] parts) =>
        new GoldenMutation.WriteParts(P(path), parts);

    private static GoldenMutation L(
        string path,
        string rawGid,
        Generality generality,
        string body) =>
        new GoldenMutation.Lean(P(path), rawGid, generality, body);

    private static GoldenMutation X(string path) => new GoldenMutation.Delete(P(path));

    private static GoldenMutation A(string path, int count, string line) =>
        new GoldenMutation.AppendLines(P(path), count, line);

    private static GoldenMutation Domain(string name, Stratum stratum)
    {
        if (!DomainId.TryCreate(name, out var domain))
        {
            throw new ArgumentException("Invalid fixture domain.", nameof(name));
        }

        return new GoldenMutation.AddDomain(domain, stratum);
    }

    private static GoldenMutation T(string path, string rawGid, string rawCaseId) =>
        new GoldenMutation.AddTask(P(path), rawGid, rawCaseId);

    private static GoldenMutation Dir() => new GoldenMutation.PopulateDirectory();

    private static GoldenMutation Waiver() => new GoldenMutation.EmptyMirrorWaiver();

    private static GoldenMutation Mirror(bool json, bool yaml) =>
        new GoldenMutation.EvidenceMirror(json, yaml);

    private static GoldenMutation Replace(string oldValue, string newValue) =>
        new GoldenMutation.ReplaceBackfill(oldValue, newValue);

    private static GoldenMutation Disposition(string rawGid) =>
        new GoldenMutation.ReplaceFirstBackfillDisposition(rawGid);

    private static GoldenMutation Anchor(string anchor, bool duplicate) =>
        new GoldenMutation.MutateBackfillAnchor(anchor, duplicate);

    private static RepoPath P(string path) => RepoPath.CreateKnown(path);
}

namespace StrataLint.Definitions;

internal sealed record GoldenCase(
    string Name,
    IReadOnlyList<GoldenMutation> BaselineMutations,
    IReadOnlyList<GoldenMutation> Mutations,
    IReadOnlyList<GoldenDiagnostic> ExpectedDiagnostics);

internal sealed record GoldenDiagnostic(int RuleNumber, string Path, string Message);

internal enum GoldenGenerality
{
    General,
    Instance,
    Extremal,
}

internal enum GoldenStratum
{
    S0,
    S1,
    S2,
    S3,
    S4,
}

internal abstract record GoldenMutation
{
    internal sealed record Write(string Path, string Content) : GoldenMutation;

    internal sealed record WriteParts(string Path, IReadOnlyList<string> Parts) : GoldenMutation;

    internal sealed record Lean(
        string Path,
        string RawGid,
        GoldenGenerality Generality,
        string Body) : GoldenMutation;

    internal sealed record Delete(string Path) : GoldenMutation;

    internal sealed record AppendLines(string Path, int Count, string Line) : GoldenMutation;

    internal sealed record AddDomain(string Name, GoldenStratum Stratum) : GoldenMutation;

    internal sealed record AddTask(string Path, string RawGid, string RawCaseId) : GoldenMutation;

    internal sealed record PopulateDirectory : GoldenMutation;

    internal sealed record EmptyMirrorWaiver : GoldenMutation;

    internal sealed record EvidenceMirror(bool IncludeJson, bool IncludeYaml) : GoldenMutation;

    internal sealed record ReplaceBackfill(string OldValue, string NewValue) : GoldenMutation;

    internal sealed record ReplaceFirstBackfillDisposition(string RawGid) : GoldenMutation;

    internal sealed record MutateBackfillAnchor(string Anchor, bool Duplicate) : GoldenMutation;
}

internal static partial class GoldenCorpus
{
    internal const string RingPath = "D5/S0/Carrier/Ring.lean";
    internal const string BlueprintPath = "Blueprint/D5/S0/Carrier/Ring.md";
    internal const string NotationPath = "D5/S0/Conventions/Notation.lean";
    internal const string AssumptionDebtPath = "D5/X_Assumptions/AxiomDebt.lean";
    internal const string HeartsPath = "D5/X_Frontier/Hearts.lean";

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
        new(rule, path, message);

    private static GoldenMutation W(string path, string content) =>
        new GoldenMutation.Write(path, content);

    private static GoldenMutation WP(string path, params string[] parts) =>
        new GoldenMutation.WriteParts(path, parts);

    private static GoldenMutation L(
        string path,
        string rawGid,
        GoldenGenerality generality,
        string body) =>
        new GoldenMutation.Lean(path, rawGid, generality, body);

    private static GoldenMutation X(string path) => new GoldenMutation.Delete(path);

    private static GoldenMutation A(string path, int count, string line) =>
        new GoldenMutation.AppendLines(path, count, line);

    private static GoldenMutation Domain(string name, GoldenStratum stratum) =>
        new GoldenMutation.AddDomain(name, stratum);

    private static GoldenMutation T(string path, string rawGid, string rawCaseId) =>
        new GoldenMutation.AddTask(path, rawGid, rawCaseId);

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
}

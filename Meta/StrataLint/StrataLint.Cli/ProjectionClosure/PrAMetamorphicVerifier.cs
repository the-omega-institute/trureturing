using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record PrAMatrixCase(
    string OutputRoot,
    string Checkout,
    string Locale,
    string Timezone,
    string Order,
    int Parallelism,
    long SourceDateEpoch);

internal sealed record PrAArtifact(
    string ArtifactId,
    string Path,
    string Mode,
    string Sha256,
    ImmutableArray<byte> Bytes);

internal sealed record PrARunSnapshot(
    ImmutableArray<PrAArtifact> Artifacts,
    string Receipt,
    string Handle,
    ImmutableDictionary<string, ImmutableArray<byte>> VerifierResults);

internal sealed record PrARealRebuildOutcome(PrARunSnapshot Snapshot, bool GeneratorRan);

internal sealed record PrAMetamorphicResult(
    bool Pass,
    int ExitCode,
    ImmutableArray<string> Diagnostics,
    int CasesRun,
    int RealRebuildsRun = 0,
    string Lane = "protocol",
    int CanaryDeferredCount = 0,
    ImmutableArray<string> DeferredEnvTuples = default);

internal static class PrAMetamorphicVerifier
{
    private static readonly string[] Locales = ["C", "en_US.UTF-8"];
    private static readonly string[] Timezones = ["UTC", "Asia/Singapore"];
    private static readonly string[] Orders = ["canonical", "reverse", "seeded-shuffle"];
    private static readonly int[] Parallelism = [1, 4];
    private static readonly long[] Epochs = [0, 1];
    private static readonly string[] OutputRoots = ["output-root-a", "output-root-b"];
    private static readonly string[] Checkouts = ["checkout-a", "checkout-b"];

    internal static PrAMetamorphicResult Verify(Func<PrAMatrixCase, PrARunSnapshot> produce)
        => VerifyCore(produce, realRebuild: false);

    internal static PrAMetamorphicResult VerifyRequired(Func<PrAMatrixCase, PrARealRebuildOutcome> produce)
    {
        var realRebuilds = 0;
        var result = VerifyCore(testCase =>
        {
            var canonical = testCase with
            {
                Locale = "C",
                Timezone = "UTC",
                Order = "canonical",
                Parallelism = 1,
                SourceDateEpoch = 0,
            };
            var outcome = produce(canonical);
            if (outcome.GeneratorRan) realRebuilds++;
            return outcome.Snapshot;
        }, realRebuild: false);
        var deferred = CanaryScope().Select(DescribeEnvironment).ToImmutableArray();
        if (realRebuilds != 2)
        {
            result = result with
            {
                Pass = false,
                ExitCode = 1,
                Diagnostics = result.Diagnostics.Add($"M-REBUILD-COUNT expected=2 actual={realRebuilds}"),
            };
        }
        return result with
        {
            RealRebuildsRun = realRebuilds,
            Lane = "required",
            CanaryDeferredCount = deferred.Length,
            DeferredEnvTuples = deferred,
        };
    }

    internal static ImmutableArray<PrAMatrixCase> RequiredScope() =>
    [
        CanonicalEnvironment("checkout-a"),
        CanonicalEnvironment("checkout-b"),
    ];

    internal static ImmutableArray<PrAMatrixCase> CanaryScope() => EnvironmentCases()
        .Except(RequiredScope())
        .ToImmutableArray();

    internal static PrAMetamorphicResult VerifyCanary(Func<PrAMatrixCase, PrARealRebuildOutcome> produce)
    {
        ArgumentNullException.ThrowIfNull(produce);
        var diagnostics = ImmutableArray.CreateBuilder<string>();
        PrARunSnapshot? baseline = null;
        byte[]? baselineReceiptProjection = null;
        byte[]? baselineHandleProjection = null;
        var rebuilds = 0;
        var cases = 0;
        foreach (var testCase in CanaryScope())
        {
            try
            {
                var outcome = produce(testCase);
                if (outcome.GeneratorRan) rebuilds++;
                ValidateSnapshot(outcome.Snapshot);
                var receiptProjection = ClockReceiptProjection(outcome.Snapshot.Receipt);
                var handleProjection = ClockHandleProjection(outcome.Snapshot.Handle);
                if (baseline is null)
                {
                    baseline = outcome.Snapshot;
                    baselineReceiptProjection = receiptProjection;
                    baselineHandleProjection = handleProjection;
                }
                if (!ArtifactsEqual(baseline.Artifacts, outcome.Snapshot.Artifacts)
                    || !VerifierResultsEqual(baseline.VerifierResults, outcome.Snapshot.VerifierResults)
                    || !baselineReceiptProjection!.AsSpan().SequenceEqual(receiptProjection)
                    || !baselineHandleProjection!.AsSpan().SequenceEqual(handleProjection))
                    diagnostics.Add($"M-EMITTER-NONDETERMINISTIC case={Describe(testCase)} output differs from canary baseline");
                cases++;
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
                or JsonException or FormatException or InvalidOperationException or ArgumentException)
            {
                diagnostics.Add($"M-EMITTER-NONDETERMINISTIC case={Describe(testCase)} invalid={exception.Message}");
                break;
            }
        }
        if (rebuilds != 94) diagnostics.Add($"M-REBUILD-COUNT expected=94 actual={rebuilds}");
        var pass = cases == 94 && rebuilds == 94 && diagnostics.Count == 0;
        return new(pass, pass ? 0 : 1, diagnostics.ToImmutable(), cases, rebuilds, "canary", 0, []);
    }

    private static PrAMetamorphicResult VerifyCore(
        Func<PrAMatrixCase, PrARunSnapshot> produce,
        bool realRebuild)
    {
        ArgumentNullException.ThrowIfNull(produce);
        var diagnostics = ImmutableArray.CreateBuilder<string>();
        PrARunSnapshot? baseline = null;
        byte[]? baselineReceiptProjection = null;
        byte[]? baselineHandleProjection = null;
        var casesRun = 0;

        foreach (var testCase in Cases())
        {
            PrARunSnapshot snapshot;
            try
            {
                snapshot = produce(testCase);
                ValidateSnapshot(snapshot);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
                or JsonException or FormatException or InvalidOperationException or ArgumentException)
            {
                diagnostics.Add($"M-EMITTER-NONDETERMINISTIC case={Describe(testCase)} invalid={exception.Message}");
                break;
            }

            casesRun++;
            var receiptProjection = ClockReceiptProjection(snapshot.Receipt);
            var handleProjection = ClockHandleProjection(snapshot.Handle);
            if (baseline is null)
            {
                baseline = snapshot;
                baselineReceiptProjection = receiptProjection;
                baselineHandleProjection = handleProjection;
                continue;
            }

            if (!ArtifactsEqual(baseline.Artifacts, snapshot.Artifacts)
                || !VerifierResultsEqual(baseline.VerifierResults, snapshot.VerifierResults)
                || !baselineReceiptProjection!.AsSpan().SequenceEqual(receiptProjection)
                || !baselineHandleProjection!.AsSpan().SequenceEqual(handleProjection))
            {
                diagnostics.Add($"M-EMITTER-NONDETERMINISTIC case={Describe(testCase)} output differs from baseline");
            }
        }

        var pass = casesRun == 192 && diagnostics.Count == 0;
        if (casesRun != 192)
        {
            diagnostics.Add($"M-EMITTER-NONDETERMINISTIC fixed matrix incomplete expected=192 actual={casesRun}");
        }

        return new PrAMetamorphicResult(
            pass,
            pass ? 0 : 1,
            diagnostics.ToImmutable(),
            casesRun,
            realRebuild ? casesRun : 0);
    }

    private static IEnumerable<PrAMatrixCase> Cases()
    {
        foreach (var outputRoot in OutputRoots)
        foreach (var checkout in Checkouts)
        foreach (var locale in Locales)
        foreach (var timezone in Timezones)
        foreach (var order in Orders)
        foreach (var parallelism in Parallelism)
        foreach (var epoch in Epochs)
        {
            yield return new PrAMatrixCase(
                outputRoot, checkout, locale, timezone, order, parallelism, epoch);
        }
    }

    private static IEnumerable<PrAMatrixCase> EnvironmentCases()
    {
        foreach (var checkout in Checkouts)
        foreach (var locale in Locales)
        foreach (var timezone in Timezones)
        foreach (var order in Orders)
        foreach (var parallelism in Parallelism)
        foreach (var epoch in Epochs)
            yield return new PrAMatrixCase("output-root-a", checkout, locale, timezone, order, parallelism, epoch);
    }

    private static PrAMatrixCase CanonicalEnvironment(string checkout) =>
        new("output-root-a", checkout, "C", "UTC", "canonical", 1, 0);

    private static void ValidateSnapshot(PrARunSnapshot snapshot)
    {
        if (snapshot.Artifacts.IsDefaultOrEmpty)
        {
            throw new FormatException("artifact set is empty");
        }

        var keys = new HashSet<string>(StringComparer.Ordinal);
        foreach (var artifact in snapshot.Artifacts)
        {
            if (!keys.Add($"{artifact.Path}\0{artifact.ArtifactId}"))
            {
                throw new FormatException("artifact identity/path is duplicated");
            }

            if (!ProjectionClosureValidator.IsSha256(artifact.Sha256)
                || Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(artifact.Bytes.AsSpan())) != artifact.Sha256)
            {
                throw new FormatException($"artifact digest mismatch: {artifact.ArtifactId}");
            }
        }

        _ = ClockReceiptProjection(snapshot.Receipt);
        _ = ClockHandleProjection(snapshot.Handle);
    }

    private static bool ArtifactsEqual(
        ImmutableArray<PrAArtifact> left,
        ImmutableArray<PrAArtifact> right) =>
        left.Length == right.Length
        && left.OrderBy(Key, StringComparer.Ordinal).Zip(right.OrderBy(Key, StringComparer.Ordinal))
            .All(static pair => pair.First.ArtifactId == pair.Second.ArtifactId
                && pair.First.Path == pair.Second.Path
                && pair.First.Mode == pair.Second.Mode
                && pair.First.Sha256 == pair.Second.Sha256
                && pair.First.Bytes.AsSpan().SequenceEqual(pair.Second.Bytes.AsSpan()));

    private static bool VerifierResultsEqual(
        ImmutableDictionary<string, ImmutableArray<byte>> left,
        ImmutableDictionary<string, ImmutableArray<byte>> right) =>
        left.Count == right.Count
        && left.All(item => right.TryGetValue(item.Key, out var bytes)
            && item.Value.AsSpan().SequenceEqual(bytes.AsSpan()));

    private static byte[] ClockReceiptProjection(string json) => Project(
        json,
        "receipt-v1",
        ["source_date_epoch", "request_sha256", "cross_artifact_sha256"]);

    private static byte[] ClockHandleProjection(string json) => Project(
        json,
        "run-handle-v1",
        ["request_sha256", "receipt_sha256"]);

    private static byte[] Project(string json, string schema, string[] excluded)
    {
        var node = JsonNode.Parse(json, documentOptions: new JsonDocumentOptions
        {
            AllowTrailingCommas = false,
            CommentHandling = JsonCommentHandling.Disallow,
        }) as JsonObject ?? throw new FormatException($"{schema} must be an object");
        if (node["schema"]?.GetValue<string>() != schema)
        {
            throw new FormatException($"expected {schema}");
        }

        foreach (var field in excluded)
        {
            if (!node.Remove(field))
            {
                throw new FormatException($"{schema} missing {field}");
            }
        }

        using var document = JsonDocument.Parse(node.ToJsonString());
        return StructuredCanonicalWriter.WriteJson(document.RootElement).ToArray();
    }

    private static string Key(PrAArtifact artifact) => $"{artifact.Path}\0{artifact.ArtifactId}";

    private static string Describe(PrAMatrixCase item) =>
        $"root={item.OutputRoot},checkout={item.Checkout},locale={item.Locale},timezone={item.Timezone},order={item.Order},parallel={item.Parallelism},epoch={item.SourceDateEpoch}";

    internal static string DescribeEnvironment(PrAMatrixCase item) =>
        $"checkout={item.Checkout},locale={item.Locale},timezone={item.Timezone},order={item.Order},parallel={item.Parallelism},epoch={item.SourceDateEpoch}";
}

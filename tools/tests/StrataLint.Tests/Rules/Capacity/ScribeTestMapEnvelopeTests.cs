using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed class ScribeTestMapEnvelopeTests
{
    private static readonly ScribeTestMapEnvironment Environment =
        new("test-rid", ".NET test framework", "/test/dotnet", "10.0.100-test", Digest('e'));

    [Fact]
    public void RoundTripPreservesEveryFieldAndOrder()
    {
        var original = ScribeTestMapEnvelope.Create(Digest('a'), Digest('d'), Environment, CompleteMap());

        var accepted = ScribeTestMapEnvelope.TryRead(
            original.Write(),
            out var decoded,
            out var reason);

        Assert.True(accepted, reason);
        Assert.NotNull(decoded);
        Assert.Equal(1, decoded.SchemaVersion);
        Assert.Equal(original.InputDigest, decoded.InputDigest);
        Assert.Equal(original.MetadataDigest, decoded.MetadataDigest);
        Assert.Equal(original.Producer, decoded.Producer);
        Assert.Equal(Environment, decoded.Environment);
        Assert.Equal(
            original.Map.Methods.Select(MethodProjection),
            decoded.Map.Methods.Select(MethodProjection));
        Assert.Equal(
            original.Map.UnclassifiedManagedProjectPaths,
            decoded.Map.UnclassifiedManagedProjectPaths);
        Assert.Equal(
            original.Map.OrphanManagedSourcePaths,
            decoded.Map.OrphanManagedSourcePaths);
        Assert.Equal(
            original.Map.DanglingCompileFailProofProjectExemptionPaths,
            decoded.Map.DanglingCompileFailProofProjectExemptionPaths);
        Assert.Equal(
            original.Map.CompileQueryFindings,
            decoded.Map.CompileQueryFindings);
    }

    [Fact]
    public void CanonicalBytesAreStableUnderReencode()
    {
        var bytes = ScribeTestMapEnvelope.Create(
            Digest('b'),
            Digest('d'),
            Environment,
            CompleteMap()).Write();
        using var document = JsonDocument.Parse(bytes);

        var reencoded = StructuredCanonicalWriter.WriteJson(document.RootElement).ToArray();

        Assert.Equal(bytes, reencoded);
    }

    [Fact]
    public void RejectsSchemaVersionOtherThanOne()
    {
        var bytes = Rewrite(ValidBytes(), root => root["schema_version"] = 2);

        var accepted = ScribeTestMapEnvelope.TryRead(bytes, out _, out var reason);

        Assert.False(accepted);
        Assert.Contains("schema-version", reason, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsUnknownReasonName()
    {
        var bytes = Rewrite(ValidBytes(), root =>
        {
            var reasons = root["map"]!["methods"]![0]!["unknown_reasons"]!.AsArray();
            reasons[0] = "FutureReason";
        });

        var accepted = ScribeTestMapEnvelope.TryRead(bytes, out _, out var reason);

        Assert.False(accepted);
        Assert.Contains("unknown-reason", reason, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsUnknownOrMissingField()
    {
        var unknown = Rewrite(ValidBytes(), root => root["future_field"] = true);
        var missing = Rewrite(ValidBytes(), root => root.Remove("producer"));

        foreach (var bytes in new[] { unknown, missing })
        {
            var accepted = ScribeTestMapEnvelope.TryRead(bytes, out _, out var reason);

            Assert.False(accepted);
            Assert.Contains("field", reason, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void RejectsNonCanonicalBytes()
    {
        var canonical = ValidBytes();
        var bytes = new byte[canonical.Length + 1];
        bytes[0] = (byte)' ';
        canonical.CopyTo(bytes, 1);

        var accepted = ScribeTestMapEnvelope.TryRead(bytes, out _, out var reason);

        Assert.False(accepted);
        Assert.Contains("noncanonical", reason, StringComparison.Ordinal);
    }

    private static byte[] ValidBytes() =>
        ScribeTestMapEnvelope.Create(Digest('c'), Digest('d'), Environment, CompleteMap()).Write();

    private static byte[] Rewrite(byte[] bytes, Action<JsonObject> rewrite)
    {
        var root = Assert.IsType<JsonObject>(
            JsonNode.Parse(Encoding.UTF8.GetString(bytes)));
        rewrite(root);
        return StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(root)).ToArray();
    }

    private static ScribeTestMap CompleteMap() => new(
        [
            new ScribeTestMethod(
                "partition-z",
                "tools/tests/ZTests.cs",
                "ZTests.Second",
                Enum.GetValues<TestMapUnknownReason>()),
            new ScribeTestMethod(
                "partition-a",
                "tools/tests/ATests.cs",
                "ATests.First",
                [TestMapUnknownReason.Other, TestMapUnknownReason.VariablePath]),
        ],
        ["tools/tests/Z.csproj", "tools/tests/A.csproj"],
        ["tools/tests/ZOrphan.cs", "tools/tests/AOrphan.cs"],
        ["tools/tests/ZProof.csproj", "tools/tests/AProof.csproj"],
        [
            new MsBuildCompileFinding("tools/tests/Z.csproj", "z finding"),
            new MsBuildCompileFinding("tools/tests/A.csproj", "a finding"),
        ]);

    private static (string PartitionKey, string SourcePath, string Id, string UnknownReasons)
        MethodProjection(ScribeTestMethod method) =>
        (
            method.PartitionKey,
            method.SourcePath,
            method.Id,
            string.Join(',', method.UnknownReasons));

    private static string Digest(char value) => new(value, 64);
}

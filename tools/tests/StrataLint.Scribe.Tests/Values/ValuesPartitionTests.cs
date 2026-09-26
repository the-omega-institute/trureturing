using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ValuesPartitionTests
{
    [Theory]
    [InlineData("D5/Bh")]
    [InlineData("D5/T1")]
    public void AcceptedSingleRowChangesExactlyItsCompleteShardBytes(string id)
    {
        WithCatalog(root =>
        {
            var before = CanonicalValuesWriter.Write(root);
            WriteCatalog(root, Catalog(id == "D5/Bh" ? "changed" : "first", id == "D5/T1" ? "changed" : "second"));
            var after = CanonicalValuesWriter.Write(root);
            Assert.Equal([ValuesProjectionAddress.PathFor(id)], before.Zip(after)
                .Where(pair => !pair.First.Bytes.AsSpan().SequenceEqual(pair.Second.Bytes.AsSpan()))
                .Select(pair => pair.First.RelativePath).ToArray());
            AssertDeterministic(root, after);
        });
    }

    [Fact]
    public void UnusedAcceptedParametersRemainVisibleInCompleteNormalizedInput()
    {
        WithCatalog(root =>
        {
            var before = CanonicalValuesWriter.Write(root);
            WriteCatalog(root, Catalog().Replace("term_count = 1", "term_count = 2", StringComparison.Ordinal));
            var after = CanonicalValuesWriter.Write(root);
            using var first = JsonDocument.Parse(before[0].Bytes.AsMemory());
            using var second = JsonDocument.Parse(after[0].Bytes.AsMemory());
            Assert.Equal(first.RootElement.GetProperty("constant").GetRawText(), second.RootElement.GetProperty("constant").GetRawText());
            Assert.Equal(2, second.RootElement.GetProperty("input").GetProperty("term_count").GetInt32());
            Assert.False(before[0].Bytes.AsSpan().SequenceEqual(after[0].Bytes.AsSpan()));
            Assert.Equal(before[1].Bytes.ToArray(), after[1].Bytes.ToArray());
            Assert.Equal("not-kernel-evaluated:noncomputable-real", second.RootElement
                .GetProperty("attestation").GetProperty("consistency").GetProperty("numeric_binding").GetString());
            Assert.Equal("gid+kind=def+std3+statement-sha256", second.RootElement
                .GetProperty("attestation").GetProperty("consistency").GetProperty("lean_binding").GetString());
            Assert.False(second.RootElement.GetProperty("attestation").TryGetProperty("input_sha256", out _));
            Assert.Equal("D5/S3/Constants/Values.bh", second.RootElement.GetProperty("attestation").GetProperty("provenance").GetString());
        });
    }

    [Fact]
    public void AddingAndRemovingKeysChangesOnlyTheirPathsAndInventoryWithoutEvaluation()
    {
        WithCatalog(root =>
        {
            var original = CanonicalValuesWriter.Write(root);
            var originalInput = Catalog();
            var extra = Row("D5/Ω/../😀", "extra", "extra");
            WriteCatalog(root, originalInput + extra);
            var expanded = CanonicalValuesWriter.Write(root);
            Assert.Equal(3, expanded.Length);
            Assert.Equal(original[0].Bytes.ToArray(), expanded[0].Bytes.ToArray());
            Assert.Equal(original[1].Bytes.ToArray(), expanded[1].Bytes.ToArray());
            Assert.Equal(0, ValuesEmitter.Emit(root, false, TextWriter.Null, TextWriter.Null));
            var extraPath = ValuesProjectionAddress.PathFor("D5/Ω/../😀");
            Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(root, extraPath)));
            Assert.Contains(Inventory(root), artifact => artifact.Path == extraPath && artifact.ArtifactId == "none");
            WriteCatalog(root, originalInput);
            Assert.DoesNotContain(Inventory(root), artifact => artifact.Path == extraPath);
            Assert.Equal(0, ValuesEmitter.Emit(root, false, TextWriter.Null, TextWriter.Null));
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, extraPath)));
            AssertDeterministic(root, original);

            // Loader accepts this specification; numerical evaluation cannot produce the required
            // four windows. Inventory and snapshot identity must never invoke that evaluation.
            WriteCatalog(root, "schema_version = 1\n" + Row("D5/Cphi", "cphi", "unused")
                .Replace("registered-open", "emitted", StringComparison.Ordinal)
                .Replace("open_reason = \"unused\"", "error = \"0\"", StringComparison.Ordinal)
                .Replace("computation = \"none\"", "computation = \"cphi\"\nterm_count = 12\nfractional_part_decimal_digits = 30\nfirst_fibonacci_index = 5\nlast_fibonacci_index = 5", StringComparison.Ordinal));
            Assert.Contains(Inventory(root), artifact => artifact.Path == ValuesProjectionAddress.PathFor("D5/Cphi"));
            Assert.Throws<InvalidOperationException>(() => CanonicalValuesWriter.Write(root));
            Assert.NotEmpty(SnapshotContentDigest.Compute(Snapshot(root, "snapshot"), []));
        });
    }

    [Fact]
    public void SnapshotDigestUsesItsOwnCatalogAndExcludesOnlyAuthoritativeShardBytes()
    {
        WithCatalog(root =>
        {
            var first = SnapshotContentDigest.Compute(Snapshot(root, "first"), []);
            Assert.Equal(first, SnapshotContentDigest.Compute(Snapshot(root, "stale"), []));
            var bogus = ValuesProjectionAddress.PathFor("not-in-catalog");
            Assert.NotEqual(SnapshotContentDigest.Compute(Snapshot(root, "same", bogus, "first"), []),
                SnapshotContentDigest.Compute(Snapshot(root, "same", bogus, "second"), []));
            WriteCatalog(root, Catalog("new source"));
            Assert.NotEqual(first, SnapshotContentDigest.Compute(Snapshot(root, "first"), []));
        });
    }

    [Fact]
    public void ProducerRejectsKeyPayloadAndPathSubstitution()
    {
        WithCatalog(root =>
        {
            var row = CanonicalValuesWriter.Write(root)[0];
            Assert.Throws<FormatException>(() => CanonicalValuesWriter.ValidateBinding(row with { RelativePath = ValuesProjectionAddress.PathFor("D5/T1") }));
            Assert.Throws<FormatException>(() => CanonicalValuesWriter.ValidateBinding(row with { Id = "D5/T1" }));
            var payload = Encoding.UTF8.GetString(row.Bytes.AsSpan()).Replace("D5/Bh", "D5/T1", StringComparison.Ordinal);
            Assert.Throws<FormatException>(() => CanonicalValuesWriter.ValidateBinding(row with { Bytes = Encoding.UTF8.GetBytes(payload).ToImmutableArray() }));
        });
    }

    [Fact]
    public void InputFormattingAndGlobalUnrelatedFilesDoNotChangeShards()
    {
        WithCatalog(root =>
        {
            var original = CanonicalValuesWriter.Write(root);
            WriteCatalog(root, "# formatting only\n" + Catalog().Replace("term_count = 1", "term_count=1 # comment", StringComparison.Ordinal));
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, "global.json"), "unrelated bytes\n");
            AssertDeterministic(root, original);
        });
    }

    private static ImmutableArray<GeneratedArtifactIdentity> Inventory(string root) =>
        GeneratedArtifactInventory.Create(Array.Empty<string>(), CanonicalValuesWriter.MutationKeys(root));

    private static RepositorySnapshot Snapshot(string root, string shardBytes, string? extraPath = null, string extraBytes = "")
    {
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(ValuesKernelDataLoader.RelativePath, TemporaryFileSystem.File.ReadAllText(Path.Combine(root, ValuesKernelDataLoader.RelativePath))),
        };
        entries.AddRange(ValuesKernelDataLoader.LoadRepository(root).Select(row => RawRepositoryEntry.FromText(ValuesProjectionAddress.PathFor(row.Id), shardBytes)));
        if (extraPath is not null) entries.Add(RawRepositoryEntry.FromText(extraPath, extraBytes));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
    }

    private static void AssertDeterministic(string root, ImmutableArray<ValuesProjection> expected)
    {
        var actual = CanonicalValuesWriter.Write(root);
        Assert.Equal(expected.Select(row => row.RelativePath), actual.Select(row => row.RelativePath));
        foreach (var pair in expected.Zip(actual)) Assert.Equal(pair.First.Bytes.ToArray(), pair.Second.Bytes.ToArray());
    }

    private static string Catalog(string first = "first", string second = "second") =>
        "schema_version = 1\n" + Row("D5/Bh", "bh", first) + "term_count = 1\n" + Row("D5/T1", "t1", second);

    private static string Row(string id, string declaration, string reason) => $$"""

        [[constants]]
        id = "{{id}}"
        lean_gid = "D5/S3/Constants/Values.{{declaration}}"
        lean_statement_sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        status = "registered-open"
        definition = "synthetic value"
        method = "synthetic"
        reference_value = "0"
        reference_error = "0"
        open_reason = "{{reason}}"
        refs = {}
        computation = "none"
        """ + "\n";

    private static void WriteCatalog(string root, string catalog) => TemporaryFileSystem.File.WriteAllText(Path.Combine(root, ValuesKernelDataLoader.RelativePath), catalog);

    private static void WithCatalog(Action<string> run)
    {
        var directory = TemporaryFileSystem.Directory.CreateTempSubdirectory("values-partitions-");
        try
        {
            TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(directory.FullName, "Golden"));
            WriteCatalog(directory.FullName, Catalog());
            run(directory.FullName);
        }
        finally { directory.Delete(recursive: true); }
    }
}

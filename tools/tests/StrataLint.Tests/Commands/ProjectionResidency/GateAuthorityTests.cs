using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class GateAuthorityTests
{
    private const string OldBuild =
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

    // The literal is a shrink sentinel, not a restatement of roots.Length. These roots are
    // an authority selection, not every stage in the entrypoints: harness-gate.sh marks
    // restore-judge and the Makefile carries dozens of targets, none of which the catalog
    // admits. Comparing the count against the collection it came from would assert nothing
    // and would let a root be dropped silently. Retiring one is a deliberate act: change the
    // number here in the same commit.
    [Fact]
    public void RepositoryCatalogHasFourteenUniqueUtf8SortedRoots()
    {
        var roots = GateAuthorityRootCatalogLoader.LoadRepository(TestRepositoryLayout.FindRoot());

        Assert.Equal(14, roots.Length);
        Assert.Equal(
            roots.Length,
            roots.Select(root => root.RootId).Distinct().Count());
        Assert.Equal(
            roots.Select(root => root.RootId),
            roots.Select(root => root.RootId)
                .OrderBy(value => Encoding.UTF8.GetBytes(value), ByteArrayComparer.Instance));
    }

    [Fact]
    public void CatalogLoaderAcceptsClosedSyntheticCatalog()
    {
        var roots = GateAuthorityRootCatalogLoader.Parse(Encoding.UTF8.GetBytes("""
            schema = "gate-authority-roots-v1"

            [[roots]]
            root_id = "Delta/check"
            entrypoint = "Delta/check.sh"

            [[roots]]
            root_id = "Epsilon/check"
            entrypoint = "Epsilon/check.sh"

            [[roots]]
            root_id = "Zeta/check"
            entrypoint = "Zeta/check.sh"
            """ + "\n"));

        Assert.Equal(["Delta/check", "Epsilon/check", "Zeta/check"],
            roots.Select(static root => root.RootId));
    }

    [Theory]
    [InlineData("schema = \"gate-authority-roots-v1\"\nextra = true\n")]
    [InlineData("schema = \"gate-authority-roots-v1\"\n[[roots]]\nroot_id = \"Delta/check\"\n")]
    [InlineData("schema = \"gate-authority-roots-v1\"\n[[roots]]\nroot_id = \"Delta/check\"\nentrypoint = \"../check.sh\"\n")]
    [InlineData("schema = \"gate-authority-roots-v1\"\n[[roots]]\nroot_id = \"Delta/check\"\nentrypoint = \"Delta/check.sh\"\n[[roots]]\nroot_id = \"Delta/check\"\nentrypoint = \"Epsilon/check.sh\"\n")]
    [InlineData("schema = \"gate-authority-roots-v1\"\n[[roots]]\nroot_id = \"Zeta/check\"\nentrypoint = \"Zeta/check.sh\"\n[[roots]]\nroot_id = \"Delta/check\"\nentrypoint = \"Delta/check.sh\"\n")]
    public void CatalogLoaderRejectsOpenMalformedUnsafeDuplicateOrUnsortedData(string text)
    {
        Assert.Throws<FormatException>(() =>
            GateAuthorityRootCatalogLoader.Parse(Encoding.UTF8.GetBytes(text)));
    }

    [Fact]
    public void EntrypointsExistAndEveryRootBindsTheCompleteFileBytes()
    {
        var root = TestRepositoryLayout.FindRoot();
        var authority = GateAuthorityProducer.Create(root, OldBuild);

        foreach (var item in authority.Roots)
        {
            var path = Path.Combine(root, item.Entrypoint.Replace('/', Path.DirectorySeparatorChar));
            Assert.True(File.Exists(path), $"missing entrypoint {item.Entrypoint}");
            Assert.Equal(
                Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path))),
                item.EntrypointBlobSha256);
        }
    }

    // The entrypoint check above proves the FILE is there, which is the easy half: when
    // #1116 deleted the emit-check target and the echo-verify gate step, all three
    // entrypoints (Makefile, harness-gate.sh, local-harness-gate.sh) still existed and
    // five root_ids kept naming targets that were gone. gate-authority does not fail
    // closed on such a root - it hashes the entrypoint blob and emits the root_id
    // verbatim - so the catalog silently described five things that no longer existed
    // and had to be cleaned up by hand. A root_id names a target inside its entrypoint,
    // so requiring the name to still appear there is the cheapest signal that the target
    // survives. Counter-checked before it was written: all five retired suffixes occur
    // zero times in their entrypoints today, and all sixteen surviving roots pass.
    [Fact]
    public void EveryRootIdNamesSomethingItsEntrypointStillMentions()
    {
        var root = TestRepositoryLayout.FindRoot();
        var roots = GateAuthorityRootCatalogLoader.LoadRepository(root);

        foreach (var item in roots)
        {
            var separator = item.RootId.IndexOf('/', StringComparison.Ordinal);
            Assert.True(separator > 0, $"root id {item.RootId} has no target segment");
            var target = item.RootId[(separator + 1)..];
            var body = File.ReadAllText(
                Path.Combine(root, item.Entrypoint.Replace('/', Path.DirectorySeparatorChar)),
                Encoding.UTF8);

            Assert.True(
                body.Contains(target, StringComparison.Ordinal),
                $"root {item.RootId} names a target its entrypoint {item.Entrypoint} "
                    + "no longer mentions; the root is stale or the target was renamed");
        }
    }

    [Fact]
    public void StrictReaderRejectsExtraMissingReorderedAndDuplicateFields()
    {
        var canonical = ProduceBytes();
        using var document = JsonDocument.Parse(canonical);
        var root = document.RootElement;
        var roots = root.GetProperty("roots").GetRawText();
        var oldBuild = root.GetProperty("old_build_sha256").GetString();
        var first = root.GetProperty("roots")[0];
        var malformed = new[]
        {
            $"{{\"schema\":\"expected-gate-authority-v1\",\"old_build_sha256\":\"{oldBuild}\",\"roots\":{roots},\"extra\":true}}",
            $"{{\"schema\":\"expected-gate-authority-v1\",\"roots\":{roots}}}",
            $"{{\"old_build_sha256\":\"{oldBuild}\",\"schema\":\"expected-gate-authority-v1\",\"roots\":{roots}}}",
            $"{{\"schema\":\"expected-gate-authority-v1\",\"schema\":\"expected-gate-authority-v1\",\"old_build_sha256\":\"{oldBuild}\",\"roots\":{roots}}}",
            $"{{\"schema\":\"expected-gate-authority-v1\",\"old_build_sha256\":\"{oldBuild}\",\"roots\":[{{\"entrypoint\":{JsonSerializer.Serialize(first.GetProperty("entrypoint").GetString())},\"root_id\":{JsonSerializer.Serialize(first.GetProperty("root_id").GetString())},\"entrypoint_blob_sha256\":{JsonSerializer.Serialize(first.GetProperty("entrypoint_blob_sha256").GetString())}}}]}}",
        };

        foreach (var json in malformed)
        {
            Assert.Equal(2, ValidateAuthority(Encoding.UTF8.GetBytes(json), null));
        }
    }

    [Fact]
    public void ProducerIsByteDeterministic()
    {
        Assert.Equal(ProduceBytes(), ProduceBytes());
    }

    [Fact]
    public void DeletingEachRootIsSchemaExitTwo()
    {
        var bytes = ProduceBytes();
        using var document = JsonDocument.Parse(bytes);
        var roots = document.RootElement.GetProperty("roots").EnumerateArray().ToArray();

        for (var removed = 0; removed < roots.Length; removed++)
        {
            var mutation = WriteMutation(
                OldBuild,
                roots.Where((_, index) => index != removed));
            Assert.Equal(2, ValidateAuthority(mutation, null));
        }
    }

    [Fact]
    public void SynchronizedDeleteCannotOverrideIndependentApprovedAuthoritySha()
    {
        var bytes = ProduceBytes();
        var approvedSha = GateAuthorityReader.AuthoritySha256(bytes);
        using var document = JsonDocument.Parse(bytes);
        var roots = document.RootElement.GetProperty("roots").EnumerateArray().Skip(1);
        var authorityAndDiagnosticCatalogMutation = WriteMutation(OldBuild, roots);

        Assert.Equal(
            2,
            ValidateAuthority(authorityAndDiagnosticCatalogMutation, approvedSha));
    }

    [Fact]
    public void CommandRejectsMissingArgumentsAndUnwritableOutputAsUsage()
    {
        var root = TestRepositoryLayout.FindRoot();
        using var temporary = new TemporaryDirectory();
        Assert.Equal(2, GateAuthorityCommand.Run(root, null, Path.Combine(temporary.Path, "a.json")).ExitCode);
        Assert.Equal(2, GateAuthorityCommand.Run(root, OldBuild, null).ExitCode);
        Assert.Equal(2, GateAuthorityCommand.Run(root, OldBuild, temporary.Path).ExitCode);
    }

    private static byte[] ProduceBytes() =>
        GateAuthorityProducer.Write(GateAuthorityProducer.Create(TestRepositoryLayout.FindRoot(), OldBuild));

    private static int ValidateAuthority(byte[] bytes, string? expectedAuthoritySha256) =>
        GateAuthorityReader.Validate(
            bytes,
            expectedAuthoritySha256,
            GateAuthorityRootCatalogLoader.LoadRepository(TestRepositoryLayout.FindRoot()));

    private static byte[] WriteMutation(string oldBuild, IEnumerable<JsonElement> roots) =>
        StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            schema = "expected-gate-authority-v1",
            old_build_sha256 = oldBuild,
            roots = roots.Select(root => root.Clone()),
        })).ToArray();


    private sealed class ByteArrayComparer : IComparer<byte[]>
    {
        internal static readonly ByteArrayComparer Instance = new();

        public int Compare(byte[]? left, byte[]? right) =>
            (left, right) switch
            {
                (null, null) => 0,
                (null, _) => -1,
                (_, null) => 1,
                _ => left.AsSpan().SequenceCompareTo(right),
            };
    }
}

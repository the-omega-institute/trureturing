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

    private static readonly (string RootId, string Entrypoint)[] ExpectedRoots =
    [
        ("Makefile/echo-verify", "Makefile"),
        ("Makefile/emit-check", "Makefile"),
        ("Makefile/gate", "Makefile"),
        ("Makefile/preflight", "Makefile"),
        ("ci.yml/baseline-admission", ".github/workflows/ci.yml"),
        ("ci.yml/candidate-engineering", ".github/workflows/ci.yml"),
        ("ci.yml/lean-inspect", ".github/workflows/ci.yml"),
        ("harness-gate.sh/admission", ".github/scripts/harness-gate.sh"),
        ("harness-gate.sh/build-candidate", ".github/scripts/harness-gate.sh"),
        ("harness-gate.sh/build-judge", ".github/scripts/harness-gate.sh"),
        ("harness-gate.sh/conservative", ".github/scripts/harness-gate.sh"),
        ("harness-gate.sh/echo-verify", ".github/scripts/harness-gate.sh"),
        ("harness-gate.sh/selftest", ".github/scripts/harness-gate.sh"),
        ("local-harness-gate.sh/admission", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        ("local-harness-gate.sh/echo-verify-bootstrap", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        ("local-harness-gate.sh/emit-check", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        ("local-harness-gate.sh/engineering-dotnet", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        ("local-harness-gate.sh/engineering-selftest", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        ("local-harness-gate.sh/engineering-test", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        ("local-harness-gate.sh/lean-reports", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        ("local-harness-gate.sh/setup", "Meta/StrataLint/scripts/local-harness-gate.sh"),
    ];

    [Fact]
    public void RootAlphabetIsExactlyTheSpecSetUniqueAndUtf8Sorted()
    {
        Assert.Equal(21, GateAuthorityRootCatalog.All.Length);
        Assert.Equal(ExpectedRoots, GateAuthorityRootCatalog.All.Select(
            root => (root.RootId, root.Entrypoint)));
        Assert.Equal(
            GateAuthorityRootCatalog.All.Length,
            GateAuthorityRootCatalog.All.Select(root => root.RootId).Distinct().Count());
        Assert.Equal(
            GateAuthorityRootCatalog.All.Select(root => root.RootId),
            GateAuthorityRootCatalog.All.Select(root => root.RootId)
                .OrderBy(value => Encoding.UTF8.GetBytes(value), ByteArrayComparer.Instance));
    }

    [Fact]
    public void EntrypointsExistAndEveryRootBindsTheCompleteFileBytes()
    {
        var root = FindRepositoryRoot();
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
            Assert.Equal(2, GateAuthorityReader.Validate(Encoding.UTF8.GetBytes(json), null));
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
            Assert.Equal(2, GateAuthorityReader.Validate(mutation, null));
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
            GateAuthorityReader.Validate(authorityAndDiagnosticCatalogMutation, approvedSha));
    }

    [Fact]
    public void CommandRejectsMissingArgumentsAndUnwritableOutputAsUsage()
    {
        var root = FindRepositoryRoot();
        using var temporary = new TemporaryDirectory();
        Assert.Equal(2, GateAuthorityCommand.Run(root, null, Path.Combine(temporary.Path, "a.json")).ExitCode);
        Assert.Equal(2, GateAuthorityCommand.Run(root, OldBuild, null).ExitCode);
        Assert.Equal(2, GateAuthorityCommand.Run(root, OldBuild, temporary.Path).ExitCode);
    }

    private static byte[] ProduceBytes() =>
        GateAuthorityProducer.Write(GateAuthorityProducer.Create(FindRepositoryRoot(), OldBuild));

    private static byte[] WriteMutation(string oldBuild, IEnumerable<JsonElement> roots) =>
        StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            schema = "expected-gate-authority-v1",
            old_build_sha256 = oldBuild,
            roots = roots.Select(root => root.Clone()),
        })).ToArray();

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "CLAUDE.md")))
        {
            directory = directory.Parent;
        }

        return directory?.FullName ?? throw new InvalidOperationException("repository root not found");
    }

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

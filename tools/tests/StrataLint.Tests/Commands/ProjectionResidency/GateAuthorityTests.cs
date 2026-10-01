using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed class GateAuthorityTests
{
    private const string OldBuild =
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

    [Fact]
    public void RepositoryCatalogDerivesUniqueUtf8SortedRootsFromUnitsAndStaticRoots()
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var catalog = File.ReadAllBytes(Path.Combine(repositoryRoot, GateAuthorityRootCatalogLoader.RelativePath));
        var staticRoots = GateAuthorityRootCatalogLoader.Parse(catalog);
        using var registration = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(repositoryRoot, "Meta/ci-units.json")));
        var requiredUnits = registration.RootElement.GetProperty("units").EnumerateArray()
            .Where(unit => unit.GetProperty("check").ValueKind != JsonValueKind.Null).ToArray();
        var roots = GateAuthorityRootCatalogLoader.LoadRepository(repositoryRoot);

        Assert.Equal(staticRoots.Length + requiredUnits.Length, roots.Length);
        Assert.Equal(roots.Length, roots.Select(root => root.RootId).Distinct().Count());
        Assert.Equal(roots.Select(root => root.RootId), roots.Select(root => root.RootId)
            .OrderBy(value => Encoding.UTF8.GetBytes(value), ByteArrayComparer.Instance));
        Assert.All(requiredUnits, unit => Assert.Contains(roots, root =>
            root.RootId == Path.GetFileName(unit.GetProperty("workflow").GetString()) + "/" + unit.GetProperty("id").GetString()
            && root.Entrypoint == unit.GetProperty("workflow").GetString()));
        Assert.DoesNotContain(staticRoots, root => root.RootId.StartsWith("ci-", StringComparison.Ordinal));
    }

    [Fact]
    public void LoaderMergesStaticAndRequiredCiRootsAndSkipsNullChecks()
    {
        using var repository = SyntheticRepository();
        var roots = GateAuthorityRootCatalogLoader.LoadRepository(repository.Path);
        Assert.Equal(new[] { "Alpha/check", "ci-current.yml/current", "ci-fixture.yml/fixture", "entry.sh/check" },
            roots.Select(root => root.RootId));
        Assert.Equal(".github/workflows/ci-fixture.yml", roots.Single(root => root.RootId == "ci-fixture.yml/fixture").Entrypoint);
    }

    [Fact]
    public void StaticAndDerivedRootCollisionIsRejected()
    {
        using var repository = SyntheticRepository();
        File.WriteAllText(Path.Combine(repository.Path, GateAuthorityRootCatalogLoader.RelativePath),
            "schema = \"gate-authority-roots-v1\"\n[[roots]]\nroot_id = \"ci-fixture.yml/fixture\"\nentrypoint = \"entry.sh\"\n");
        Assert.Throws<FormatException>(() => GateAuthorityRootCatalogLoader.LoadRepository(repository.Path));
    }

    [Theory]
    [InlineData(null)]
    [InlineData("{")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":{}}")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":[{\"id\":\"fixture\",\"workflow\":\"../ci-fixture.yml\",\"check\":\"fixture / unit\"}]}")]
    public void RequiredCiRegistrationFailsClosed(string? text)
    {
        using var repository = SyntheticRepository();
        var path = Path.Combine(repository.Path, "Meta/ci-units.json");
        if (text is null) File.Delete(path); else File.WriteAllText(path, text);
        Assert.Equal(2, GateAuthorityCommand.Run(repository.Path, ["--check"]).ExitCode);
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
    public void CommandAcceptsOnlyTheCheckShape()
    {
        var root = TestRepositoryLayout.FindRoot();
        using var temporary = new TemporaryDirectory();
        var output = Path.Combine(temporary.Path, "authority.json");

        var missing = GateAuthorityCommand.Run(root, []);
        var retiredProducer = GateAuthorityCommand.Run(
            root,
            ["--old-build", OldBuild, "--out", output]);

        Assert.Equal(2, missing.ExitCode);
        Assert.Equal(2, retiredProducer.ExitCode);
        Assert.Equal("USAGE: StrataLint gate-authority --check\n", retiredProducer.Error);
        Assert.False(File.Exists(output));
    }

    [Fact]
    public void CheckRejectsAStaleRootTargetInASyntheticRepository()
    {
        using var repository = new TemporaryDirectory();
        WriteRegistration(repository.Path, OptionalRegistration);
        var catalog = Path.Combine(repository.Path, "Golden", "gate-authority-roots.toml");
        Directory.CreateDirectory(Path.GetDirectoryName(catalog)!);
        File.WriteAllText(catalog, """
            schema = "gate-authority-roots-v1"

            [[roots]]
            root_id = "entry.sh/check"
            entrypoint = "entry.sh"
            """ + "\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(repository.Path, "entry.sh"), "#!/bin/sh\n", new UTF8Encoding(false));

        var result = GateAuthorityCommand.Run(repository.Path, ["--check"]);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("no longer mentions", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckBindsSyntheticEntrypointBytesIntoStrictAuthority()
    {
        using var repository = new TemporaryDirectory();
        WriteRegistration(repository.Path, OptionalRegistration);
        var catalog = Path.Combine(repository.Path, "Golden", "gate-authority-roots.toml");
        Directory.CreateDirectory(Path.GetDirectoryName(catalog)!);
        File.WriteAllText(catalog, """
            schema = "gate-authority-roots-v1"

            [[roots]]
            root_id = "entry.sh/check"
            entrypoint = "entry.sh"
            """ + "\n", new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "entry.sh"),
            "#!/bin/sh\ncheck\n",
            new UTF8Encoding(false));

        var result = GateAuthorityCommand.Run(repository.Path, ["--check"]);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("roots=1", result.Output, StringComparison.Ordinal);
        Assert.Matches("authority_sha256=[0-9a-f]{64}", result.Output);
    }

    [Fact]
    public void CheckRejectsInvalidUtf8EntrypointAsSchemaExitTwo()
    {
        using var repository = new TemporaryDirectory();
        WriteRegistration(repository.Path, OptionalRegistration);
        var catalog = Path.Combine(repository.Path, "Golden", "gate-authority-roots.toml");
        Directory.CreateDirectory(Path.GetDirectoryName(catalog)!);
        File.WriteAllText(catalog, """
            schema = "gate-authority-roots-v1"

            [[roots]]
            root_id = "entry.sh/check"
            entrypoint = "entry.sh"
            """ + "\n", new UTF8Encoding(false));
        File.WriteAllBytes(Path.Combine(repository.Path, "entry.sh"), [0xff]);

        var result = GateAuthorityCommand.Run(repository.Path, ["--check"]);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("GATE_AUTHORITY_INVALID", result.Error, StringComparison.Ordinal);
    }

    private const string OptionalRegistration = """
        {"schema":"ci-units-v1","units":[{"id":"optional","workflow":".github/workflows/ci-optional.yml","check":null}]}
        """;

    private static TemporaryDirectory SyntheticRepository()
    {
        var repository = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(repository.Path, "Golden"));
        File.WriteAllText(Path.Combine(repository.Path, GateAuthorityRootCatalogLoader.RelativePath), """
            schema = "gate-authority-roots-v1"
            [[roots]]
            root_id = "Alpha/check"
            entrypoint = "entry.sh"
            [[roots]]
            root_id = "entry.sh/check"
            entrypoint = "entry.sh"
            """ + "\n");
        File.WriteAllText(Path.Combine(repository.Path, "entry.sh"), "#!/bin/sh\ncheck\n");
        WriteRegistration(repository.Path, """
            {"schema":"ci-units-v1","units":[
              {"id":"current","workflow":".github/workflows/ci-current.yml","check":"current"},
              {"id":"fixture","workflow":".github/workflows/ci-fixture.yml","check":"fixture / unit"},
              {"id":"optional","workflow":".github/workflows/ci-optional.yml","check":null}]}
            """);
        var directory = Path.Combine(repository.Path, ".github/workflows");
        Directory.CreateDirectory(directory);
        File.WriteAllText(Path.Combine(directory, "ci-current.yml"), "jobs: {current: {steps: []}}\n");
        File.WriteAllText(Path.Combine(directory, "ci-fixture.yml"), "jobs: {fixture: {uses: ./unit.yml}}\n");
        return repository;
    }

    private static void WriteRegistration(string root, string text)
    {
        Directory.CreateDirectory(Path.Combine(root, "Meta"));
        File.WriteAllText(Path.Combine(root, "Meta/ci-units.json"), text);
    }

    private static byte[] ProduceBytes()
    {
        using var repository = SyntheticRepository();
        return GateAuthorityProducer.Write(GateAuthorityProducer.Create(repository.Path, OldBuild));
    }

    private static int ValidateAuthority(byte[] bytes, string? expectedAuthoritySha256)
    {
        using var repository = SyntheticRepository();
        return GateAuthorityReader.Validate(bytes, expectedAuthoritySha256,
            GateAuthorityRootCatalogLoader.LoadRepository(repository.Path));
    }

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

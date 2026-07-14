using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class C0CeremonyTrustRootTests
{
    private const string TowerPath = "Meta/StrataLint/TOWER.yaml";
    private const string ControllerDirectory =
        "Meta/StrataLint/StrataLint.Cli/Conservative";
    private const string CliApplicationPath =
        "Meta/StrataLint/StrataLint.Cli/Commands/CliApplication.cs";
    private const string ProductionEnvironmentPath =
        "Meta/StrataLint/StrataLint.Cli/Admission/ProductionCliEnvironment.cs";
    private const string ProgramPath =
        "Meta/StrataLint/StrataLint.Cli/Program.cs";
    private const string CorpusSchemaDirectory =
        "Meta/StrataLint/StrataLint.Definitions/Golden";
    private const string CorpusDataDirectory =
        "Meta/StrataLint/Golden/cases";
    private const string GateWiringPath = ".github/scripts/harness-gate.sh";
    private const string CertificatePath =
        "Meta/StrataLint/Golden/c0-inaugural-conservative-certificate.json";

    [Fact]
    public void CanonicalSourceDiscoveryIncludesNestedFiles()
    {
        var root = Directory.CreateTempSubdirectory("stratalint-c0-source-discovery-").FullName;
        try
        {
            var nested = Path.Combine(root, "Controller", "Nested");
            Directory.CreateDirectory(nested);
            File.WriteAllText(Path.Combine(nested, "Worker.cs"), "// nested source fixture\n");

            Assert.Equal(
                ["Controller/Nested/Worker.cs"],
                EnumerateSourcePaths(root, "Controller", "*.cs"));
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void CorpusSourceDiscoveryDoesNotDependOnAFileNamePrefix()
    {
        var root = Directory.CreateTempSubdirectory("stratalint-c0-corpus-discovery-").FullName;
        try
        {
            var nested = Path.Combine(root, "Golden", "Sub");
            Directory.CreateDirectory(nested);
            File.WriteAllText(Path.Combine(nested, "Cases05.cs"), "// partial corpus fixture\n");

            Assert.Equal(
                ["Golden/Sub/Cases05.cs"],
                EnumerateSourcePaths(root, "Golden", "*.cs"));
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void CorpusDataDiscoveryIncludesNestedTomlFiles()
    {
        var root = Directory.CreateTempSubdirectory("stratalint-c0-corpus-data-").FullName;
        try
        {
            var nested = Path.Combine(root, "Cases", "Nested");
            Directory.CreateDirectory(nested);
            File.WriteAllText(Path.Combine(nested, "structure.toml"), "[[cases]]\n");

            Assert.Equal(
                ["Cases/Nested/structure.toml"],
                EnumerateSourcePaths(root, "Cases", "*.toml"));
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void TowerC0AddressesMatchTheCanonicalWorktreeBytes()
    {
        var root = RepositoryLayout.FindRoot();
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));
        var component = Assert.Single(
            loaded.Syntax.Components,
            static item => item.Id == "conservative-extension-gate-c");

        Assert.Equal("verified", component.Verification);
        Assert.Equal(
            [
                "phase1-protected-content-admission",
                "phase2-dual-harness-conservative-extension",
            ],
            component.Members.Take(2));
        Assert.Equal("open", loaded.Syntax.Bootstrap.Judge);
        Assert.Equal("ASSUMED-UNVERIFIED", loaded.Syntax.Bootstrap.Verification);

        var records = component.Members.Skip(2).Select(ParseRecord).ToArray();
        var controllerPaths = ExpectedControllerPaths(root);
        var corpusPaths = ExpectedCorpusPaths(root);
        Assert.Equal(controllerPaths.Length + corpusPaths.Length + 6, records.Length);
        AssertGitBlobRecords(
            root,
            records,
            "c0/controller",
            controllerPaths);
        AssertGitBlobRecords(
            root,
            records,
            "c0/corpus",
            corpusPaths);
        AssertGitBlobRecords(
            root,
            records,
            "c0/gate-wiring",
            [GateWiringPath]);

        var certificate = Assert.Single(records, static item =>
            item.Kind == "c0/inaugural-certificate");
        Assert.Equal(CertificatePath, certificate.Path);
        var certificateBytes = File.ReadAllBytes(Absolute(root, CertificatePath));
        Assert.Equal(Sha256(certificateBytes), certificate.Address);

        var baseCommit = Assert.Single(records, static item => item.Kind == "c0/base-commit");
        Assert.Null(baseCommit.Path);
        var ceremonyCommit = Assert.Single(records, static item =>
            item.Kind == "c0/ceremony-commit");
        Assert.Equal("convention/this-pr-merge-commit", ceremonyCommit.Address);
        Assert.Null(ceremonyCommit.Path);
        var preimageCommit = Assert.Single(records, static item =>
            item.Kind == "c0/preimage-commit");
        Assert.Null(preimageCommit.Path);
        var preimageTree = Assert.Single(records, static item => item.Kind == "c0/preimage-tree");
        Assert.Null(preimageTree.Path);

        using var document = JsonDocument.Parse(certificateBytes);
        var certificateRoot = document.RootElement;
        Assert.Equal(
            "stratalint-conservative-certificate-v1",
            certificateRoot.GetProperty("schema").GetString());
        Assert.Equal("CORPUS_CONSERVATIVE", certificateRoot.GetProperty("status").GetString());
        Assert.Empty(certificateRoot.GetProperty("findings").EnumerateArray());
        Assert.Equal(110, certificateRoot.GetProperty("golden_case_count").GetInt32());
        var implication = certificateRoot.GetProperty("positive_implication");
        Assert.Equal(
            implication.GetProperty("baseline_admit_count").GetInt32(),
            implication.GetProperty("preserved_admit_count").GetInt32());
        Assert.Equal(
            "git-commit/" + certificateRoot.GetProperty("baseline")
                .GetProperty("commit_oid").GetString(),
            baseCommit.Address);
        Assert.Equal(
            certificateRoot.GetProperty("baseline").GetProperty("tree_oid").GetString(),
            "git-sha1:" + Git(
                root,
                "rev-parse",
                Untag(baseCommit.Address, "git-commit/") + "^{tree}"));

        var candidate = certificateRoot.GetProperty("candidate");
        Assert.Equal(
            "git-commit/" + candidate.GetProperty("commit_oid").GetString(),
            preimageCommit.Address);
        Assert.Equal(
            "git-tree/" + Untag(candidate.GetProperty("tree_oid").GetString()!, "git-sha1:"),
            preimageTree.Address);
        var preimageOid = Untag(preimageCommit.Address, "git-commit/");
        Assert.Equal(
            Untag(preimageTree.Address, "git-tree/"),
            Git(root, "rev-parse", preimageOid + "^{tree}"));
        Git(root, "merge-base", "--is-ancestor", preimageOid, "HEAD");
        AssertPreimageBlobs(root, records, preimageOid);
    }

    private static void AssertPreimageBlobs(
        string root,
        IEnumerable<C0Record> records,
        string preimageCommit)
    {
        foreach (var record in records.Where(static item => item.Kind is
            "c0/controller" or "c0/corpus" or "c0/gate-wiring"))
        {
            Assert.Equal(
                record.Address,
                "git-sha1/" + Git(root, "rev-parse", $"{preimageCommit}:{record.Path}"));
        }
    }

    private static void AssertGitBlobRecords(
        string root,
        IReadOnlyList<C0Record> records,
        string kind,
        IReadOnlyList<string> expectedPaths)
    {
        var addressed = records
            .Where(item => item.Kind == kind)
            .ToDictionary(
                item => item.Path ?? throw new InvalidOperationException($"{kind} record has no path"),
                static item => item.Address,
                StringComparer.Ordinal);
        Assert.Equal(
            expectedPaths.Order(StringComparer.Ordinal).ToArray(),
            addressed.Keys.Order(StringComparer.Ordinal).ToArray());
        foreach (var path in expectedPaths)
        {
            Assert.Equal(GitBlobOid(File.ReadAllBytes(Absolute(root, path))), addressed[path]);
        }
    }

    private static string[] ExpectedControllerPaths(string root) =>
        EnumerateSourcePaths(root, ControllerDirectory, "*.cs")
            .Concat([CliApplicationPath, ProductionEnvironmentPath, ProgramPath])
            .Order(StringComparer.Ordinal)
            .ToArray();

    private static string[] ExpectedCorpusPaths(string root) =>
        EnumerateSourcePaths(root, CorpusSchemaDirectory, "*.cs")
            .Concat(EnumerateSourcePaths(root, CorpusDataDirectory, "*.toml"))
            .Order(StringComparer.Ordinal)
            .ToArray();

    private static string[] EnumerateSourcePaths(string root, string directory, string pattern) =>
        Directory.EnumerateFiles(
                Absolute(root, directory),
                pattern,
                SearchOption.AllDirectories)
            .Select(path => Relative(root, path))
            .Order(StringComparer.Ordinal)
            .ToArray();

    private static C0Record ParseRecord(string value)
    {
        var fields = value.Split(' ', StringSplitOptions.RemoveEmptyEntries);
        Assert.InRange(fields.Length, 2, 3);
        return new C0Record(
            fields[0],
            fields[1],
            fields.Length == 3 ? fields[2] : null);
    }

    private static string GitBlobOid(byte[] bytes)
    {
        var header = Encoding.ASCII.GetBytes($"blob {bytes.Length}\0");
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA1);
        hash.AppendData(header);
        hash.AppendData(bytes);
        return "git-sha1/" + Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static string Sha256(byte[] bytes) =>
        "sha256/" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static string Git(string root, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments) startInfo.ArgumentList.Add(argument);
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(
            process.ExitCode == 0,
            $"git {string.Join(' ', arguments)} exited {process.ExitCode}: {error}");
        return output.TrimEnd('\r', '\n');
    }

    private static string Untag(string value, string prefix)
    {
        Assert.StartsWith(prefix, value, StringComparison.Ordinal);
        return value[prefix.Length..];
    }

    private static string Absolute(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));

    private static string Relative(string root, string path) =>
        Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/');

    private sealed record C0Record(string Kind, string Address, string? Path);
}

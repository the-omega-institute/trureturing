using System.Diagnostics;
using System.Text.Json;
using System.Xml.Linq;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class C0CeremonyTrustRootTests
{
    private const string TowerPath = "Meta/StrataLint/TOWER.yaml";

    [Fact]
    public void CanonicalTrustRootSourceDoesNotUseCommitAncestry()
    {
        var root = RepositoryLayout.FindRoot();
        var projectDirectory = Absolute(
            root,
            "Meta/StrataLint/StrataLint.ArchitectureTests");
        AssertCompileSetIsClosed(root, projectDirectory);

        var forbidden = "--is-" + "ancestor";
        var occurrences = Directory
            .EnumerateFiles(projectDirectory, "*.cs", SearchOption.AllDirectories)
            .Where(path => !Path.GetRelativePath(projectDirectory, path)
                .Split(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar)
                .Any(static segment => segment is "bin" or "obj"))
            .Order(StringComparer.Ordinal)
            .SelectMany(path => File.ReadLines(path).Select((line, index) =>
                (Path: Path.GetRelativePath(root, path).Replace('\\', '/'),
                    Line: index + 1,
                    Text: line)))
            .Where(item => item.Text.Contains(
                forbidden,
                StringComparison.Ordinal))
            .Select(static item => $"{item.Path}:{item.Line}")
            .ToArray();

        Assert.Empty(occurrences);
    }

    private static void AssertCompileSetIsClosed(string root, string projectDirectory)
    {
        var projectFiles = new List<string>
        {
            Path.Combine(projectDirectory, "StrataLint.ArchitectureTests.csproj"),
        };

        for (var directory = new DirectoryInfo(projectDirectory);
             directory is not null && IsWithin(root, directory.FullName);
             directory = directory.Parent)
        {
            var props = Path.Combine(directory.FullName, "Directory.Build.props");
            if (File.Exists(props))
            {
                projectFiles.Add(props);
            }
        }

        var externalIncludes = projectFiles
            .SelectMany(path => XDocument.Load(path)
                .Descendants("Compile")
                .SelectMany(element => ((string?)element.Attribute("Include") ?? string.Empty)
                    .Split(';', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
                    .Select(include => (ProjectFile: path, Include: include))))
            .Where(item => IsExternalCompileInclude(projectDirectory, item.Include))
            .Select(item => $"{Path.GetRelativePath(root, item.ProjectFile).Replace('\\', '/')} -> {item.Include}")
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Empty(externalIncludes);
    }

    private static bool IsExternalCompileInclude(string projectDirectory, string include)
    {
        if (include.Contains("$(", StringComparison.Ordinal)
            || Path.IsPathRooted(include)
            || include.StartsWith('\\')
            || (include.Length >= 2 && char.IsAsciiLetter(include[0]) && include[1] == ':')
            || include.Split('/', '\\').Contains("..", StringComparer.Ordinal))
        {
            return true;
        }

        var normalized = Path.GetFullPath(include, projectDirectory);
        return !IsWithin(projectDirectory, normalized);
    }

    private static bool IsWithin(string directory, string path)
    {
        var relative = Path.GetRelativePath(directory, path);
        return relative != ".."
            && !relative.StartsWith($"..{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
            && !Path.IsPathRooted(relative);
    }

    [Fact]
    public void PreimageBlobValidationSurvivesSquashAndGarbageCollection()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            $"stratalint-c0-squash-{Guid.NewGuid():N}");
        Directory.CreateDirectory(root);
        try
        {
            Git(root, "init", "--initial-branch=preimage");
            Git(root, "config", "user.name", "C0 fixture");
            Git(root, "config", "user.email", "c0-fixture@example.invalid");

            File.WriteAllText(Absolute(root, "anchor.txt"), "base\n");
            Git(root, "add", "anchor.txt");
            Git(root, "commit", "-m", "base");
            var baseOid = Git(root, "rev-parse", "HEAD");

            File.WriteAllText(Absolute(root, "anchor.txt"), "candidate\n");
            Git(root, "add", "anchor.txt");
            Git(root, "commit", "-m", "candidate preimage");
            var preimageOid = Git(root, "rev-parse", "HEAD");
            var treeOid = Git(root, "rev-parse", "HEAD^{tree}");
            var blobOid = Git(root, "rev-parse", "HEAD:anchor.txt");

            Git(root, "checkout", "--orphan", "carrier");
            Git(root, "reset", "--hard", baseOid);
            Git(root, "read-tree", treeOid);
            Git(root, "checkout-index", "--all", "--force");
            Git(root, "commit", "-m", "squash carrier");
            Assert.Equal(treeOid, Git(root, "rev-parse", "HEAD^{tree}"));
            Git(root, "branch", "-D", "preimage");
            Git(root, "reflog", "expire", "--expire=now", "--all");
            Git(root, "gc", "--prune=now");

            Assert.NotEqual(0, GitExitCode(root, "cat-file", "-e", $"{preimageOid}^{{commit}}"));
            Assert.Equal(0, GitExitCode(root, "cat-file", "-e", $"{treeOid}^{{tree}}"));

            // Mutation pin: changing the production judge back to commitOid:path must fail here,
            // because the preimage commit is pruned while HEAD still carries its exact tree.
            var certificate = JsonSerializer.SerializeToUtf8Bytes(new
            {
                candidate = new { tree_oid = "git-sha1:" + treeOid },
            });
            C0Record[] records =
            [
                new("c0/controller", "git-sha1/" + blobOid, "anchor.txt"),
                new("c0/preimage-tree", "git-tree/" + treeOid, null),
            ];
            C0CeremonyTrustRootJudge.AssertPreimageBlobs(root, certificate, records);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void CanonicalTowerJudgeGraphIsClosed()
    {
        var root = RepositoryLayout.FindRoot();
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));

        var outcome = TowerManifestValidator.ValidateStructure(loaded.Syntax);

        var rejected = outcome as TowerValidationOutcome.Rejected;
        Assert.True(
            outcome is TowerValidationOutcome.Accepted,
            rejected is null
                ? "canonical TOWER returned an unknown validation outcome"
                : string.Join("; ", rejected.Findings.Select(static item =>
                    $"{item.Code} {item.Component}: {item.Message}")));
    }

    // TOWER declares what the trust root is made of: which files each component holds,
    // which rules the catalog contains, which CI jobs carry which names. A validator for
    // all of that exists and is exercised against synthetic fixtures, but nothing ran it
    // against the real repository: CoverageCommand is its only production caller and no
    // gate invokes coverage, CanonicalTowerJudgeGraphIsClosed checks structure only, and
    // the C0 evidence test below filters findings down to the C0 component. So a TOWER
    // member naming a deleted file, a rule-catalog list drifting from the real catalog,
    // or a CI job renamed out from under branch protection would all have passed. This
    // asserts the whole actual-tree validation, which is what makes the validator
    // load-bearing rather than available.
    [Fact]
    public void CanonicalTowerMatchesTheActualRepository()
    {
        var root = RepositoryLayout.FindRoot();
        var snapshot = Repository(root);
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));

        var outcome = TowerManifestValidator.Validate(
            loaded.Syntax,
            snapshot,
            RuleCatalog.Default);

        var rejected = outcome as TowerValidationOutcome.Rejected;
        Assert.True(
            outcome is TowerValidationOutcome.Accepted,
            rejected is null
                ? "canonical TOWER returned an unknown validation outcome"
                : string.Join("; ", rejected.Findings.Select(static item =>
                    $"{item.Code} {item.Component}: {item.Message}")));
    }

    [Fact]
    public void CanonicalTowerC0EvidenceIsCanonical()
    {
        var root = RepositoryLayout.FindRoot();
        var snapshot = Repository(root);
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));

        var actual = TowerActualValidator.Validate(
            loaded.Syntax,
            snapshot,
            RuleCatalog.Default);

        Assert.Empty(actual.Findings.Where(static item => string.Equals(
            item.Component,
            C0CeremonyProjection.ComponentId,
            StringComparison.Ordinal)));
    }

    [Fact]
    public void TowerC0TrustRootMatchesTheFrozenInauguralCertificate()
    {
        var root = RepositoryLayout.FindRoot();
        var snapshot = Repository(root);
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(Absolute(root, TowerPath))));
        var component = Assert.Single(
            loaded.Syntax.Components,
            static item => item.Id == C0CeremonyProjection.ComponentId);

        Assert.Equal("verified", component.Verification);
        Assert.True(C0CeremonyProjection.HasCanonicalShape(component.Members));
        Assert.Equal("open", loaded.Syntax.Bootstrap.Judge);
        Assert.Equal("ASSUMED-UNVERIFIED", loaded.Syntax.Bootstrap.Verification);

        var records = component.Members.Skip(2).Select(ParseRecord).ToArray();
        Assert.Equal(3, records.Length);

        var certificate = Assert.Single(records, static item =>
            item.Kind == "c0/inaugural-certificate");
        Assert.Equal(C0CeremonyProjection.CertificatePath, certificate.Path);
        var certificateBytes = File.ReadAllBytes(Absolute(
            root,
            C0CeremonyProjection.CertificatePath));

        var ceremonyCommit = Assert.Single(records, static item =>
            item.Kind == "c0/ceremony-commit");
        Assert.Equal("convention/this-pr-merge-commit", ceremonyCommit.Address);
        Assert.Null(ceremonyCommit.Path);
        var preimageTree = Assert.Single(records, static item => item.Kind == "c0/preimage-tree");
        Assert.Null(preimageTree.Path);

        using var document = JsonDocument.Parse(certificateBytes);
        var certificateRoot = document.RootElement;
        Assert.Equal(
            "stratalint-conservative-certificate-v1",
            certificateRoot.GetProperty("schema").GetString());
        Assert.Equal("CORPUS_CONSERVATIVE", certificateRoot.GetProperty("status").GetString());
        Assert.Empty(certificateRoot.GetProperty("findings").EnumerateArray());
        var implication = certificateRoot.GetProperty("positive_implication");
        Assert.Equal(
            implication.GetProperty("baseline_admit_count").GetInt32(),
            implication.GetProperty("preserved_admit_count").GetInt32());
        var candidate = certificateRoot.GetProperty("candidate");
        Assert.Equal(
            "git-tree/" + Untag(candidate.GetProperty("tree_oid").GetString()!, "git-sha1:"),
            preimageTree.Address);
        Assert.True(C0CeremonyProjection.TrustRootMatchesSnapshot(
            component.Members,
            snapshot,
            out var reason), reason);
    }

    private static C0Record ParseRecord(string value)
    {
        var fields = value.Split(' ', StringSplitOptions.RemoveEmptyEntries);
        Assert.InRange(fields.Length, 2, 3);
        return new C0Record(
            fields[0],
            fields[1],
            fields.Length == 3 ? fields[2] : null);
    }

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

    private static int GitExitCode(string root, params string[] arguments)
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
        process.StandardOutput.ReadToEnd();
        process.StandardError.ReadToEnd();
        process.WaitForExit();
        return process.ExitCode;
    }

    private static string Untag(string value, string prefix)
    {
        Assert.StartsWith(prefix, value, StringComparison.Ordinal);
        return value[prefix.Length..];
    }

    private static string Absolute(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));

    private static RepositorySnapshot Repository(string root) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            GitRepositorySnapshotReader.ReadCurrent(root))).Snapshot;

    internal sealed record C0Record(string Kind, string Address, string? Path);
}

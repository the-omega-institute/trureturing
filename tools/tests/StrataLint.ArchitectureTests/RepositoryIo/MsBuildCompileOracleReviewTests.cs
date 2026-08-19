namespace StrataLint.ArchitectureTests;

[Collection(MsBuildSnapshotEnvironmentCollection.Name)]
public sealed class MsBuildCompileOracleReviewTests
{
    private const string SdkProject = "<Project Sdk=\"Microsoft.NET.Sdk\" />";

    [Fact]
    public void ReviewFullPathMacVarPrivateAliasIsAdmitted()
    {
        var root = Directory.CreateTempSubdirectory("stratalint-msbuild-alias-").FullName;
        string? symbolicAlias = null;
        try
        {
            Write(root, "Actual.cs", "class Actual { }");
            var fullPath = Path.Combine(root, "Actual.cs");
            if (OperatingSystem.IsMacOS() && fullPath.StartsWith("/var/", StringComparison.Ordinal))
            {
                fullPath = "/private" + fullPath;
                Assert.StartsWith("/private/var/", fullPath, StringComparison.Ordinal);
            }
            else
            {
                symbolicAlias = root + "-link";
                Directory.CreateSymbolicLink(symbolicAlias, root);
                fullPath = Path.Combine(symbolicAlias, "Actual.cs");
            }

            var dotnet = CreateFakeDotnet(root, CompileJson(fullPath, "Wrong.cs"));
            var map = MsBuildCompileOracle.Query(root, ["App.csproj"], dotnet);

            Assert.Empty(map.Findings);
            Assert.Equal("App.csproj", map.ProjectBySourcePath["Actual.cs"]);
            Assert.DoesNotContain("Wrong.cs", map.ProjectBySourcePath.Keys);
        }
        finally
        {
            if (symbolicAlias is not null) Directory.Delete(symbolicAlias);
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void ReviewFullPathContainingDotDotBlocks()
    {
        var root = Directory.CreateTempSubdirectory("stratalint-msbuild-fullpath-").FullName;
        try
        {
            Directory.CreateDirectory(Path.Combine(root, "src", "App"));
            Write(root, "src/Source.cs", "class Source { }");
            var fullPath = root + "/src/App/../Source.cs";
            var dotnet = CreateFakeDotnet(root, CompileJson(fullPath, "../Source.cs"));

            var finding = Assert.Single(MsBuildCompileOracle.Query(
                root,
                ["src/App/App.csproj"],
                dotnet).Findings);

            Assert.Equal("src/App/App.csproj", finding.Path);
            Assert.Contains("failed closed", finding.Message, StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void ReviewSnapshotEvaluationIgnoresDirectoryBuildFilesOutsideSnapshot()
    {
        var parent = Directory.CreateTempSubdirectory("stratalint-msbuild-boundary-").FullName;
        try
        {
            var root = Path.Combine(parent, "snapshot");
            Directory.CreateDirectory(root);
            Write(parent, "Directory.Build.props", "<Project><ItemGroup><Compile Include=\"PoisonedByProps.cs\" /></ItemGroup></Project>");
            Write(parent, "Directory.Build.targets", "<Project><ItemGroup><Compile Include=\"PoisonedByTargets.cs\" /></ItemGroup></Project>");
            Write(root, "App.csproj", """
                <Project Sdk="Microsoft.NET.Sdk">
                  <PropertyGroup><EnableDefaultCompileItems>false</EnableDefaultCompileItems></PropertyGroup>
                  <ItemGroup><Compile Include="Owned.cs" /></ItemGroup>
                </Project>
                """);
            Write(root, "Owned.cs", "class Owned { }");
            Write(root, "PoisonedByProps.cs", "class PoisonedByProps { }");
            Write(root, "PoisonedByTargets.cs", "class PoisonedByTargets { }");

            var map = MsBuildCompileOracle.Query(root, ["App.csproj"]);

            Assert.Equal("App.csproj", map.ProjectBySourcePath["Owned.cs"]);
            Assert.DoesNotContain("PoisonedByProps.cs", map.ProjectBySourcePath.Keys);
            Assert.DoesNotContain("PoisonedByTargets.cs", map.ProjectBySourcePath.Keys);
        }
        finally
        {
            Directory.Delete(parent, recursive: true);
        }
    }

    [Fact]
    public void ReviewSnapshotMaterializationFailureBecomesBlockingFinding()
    {
        if (OperatingSystem.IsWindows()) return;

        var previous = Environment.GetEnvironmentVariable("TMPDIR");
        var inaccessibleRoot = Directory.CreateTempSubdirectory("stratalint-msbuild-denied-").FullName;
        File.SetUnixFileMode(inaccessibleRoot, UnixFileMode.None);
        Environment.SetEnvironmentVariable("TMPDIR", inaccessibleRoot);
        try
        {
            var map = ScribeTestMapDeriver.DeriveSnapshot(Snapshot(("App.csproj", SdkProject)));
            var finding = Assert.Single(map.CompileQueryFindings);

            Assert.Equal("App.csproj", finding.Path);
            Assert.Contains(
                ScribeUnknownDebtPolicy.InspectCurrent(map),
                candidate => candidate.Path == finding.Path && candidate.Effect == AdmissionEffect.Block);
        }
        finally
        {
            Environment.SetEnvironmentVariable("TMPDIR", previous);
            File.SetUnixFileMode(
                inaccessibleRoot,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            Directory.Delete(inaccessibleRoot, recursive: true);
        }
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Content)[] files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static file =>
            RawRepositoryEntry.FromText(file.Path, file.Content)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static byte[] CompileJson(string fullPath, string identity) =>
        System.Text.Json.JsonSerializer.SerializeToUtf8Bytes(new
        {
            Items = new { Compile = new[] { new { FullPath = fullPath, Identity = identity } } },
        });

    private static string CreateFakeDotnet(string root, byte[] output)
    {
        var outputPath = Path.Combine(root, "fake-output.bin");
        var executablePath = Path.Combine(root, "fake-dotnet");
        File.WriteAllBytes(outputPath, output);
        File.WriteAllText(executablePath, $"#!/bin/sh\n/bin/cat '{outputPath}'\nexit 0\n");
        if (!OperatingSystem.IsWindows())
        {
            File.SetUnixFileMode(
                executablePath,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        return executablePath;
    }

    private static void Write(string root, string path, string content) =>
        File.WriteAllText(Path.Combine(root, path), content);
}

[CollectionDefinition(Name, DisableParallelization = true)]
public sealed class MsBuildSnapshotEnvironmentCollection
{
    internal const string Name = "MSBuild snapshot environment";
}

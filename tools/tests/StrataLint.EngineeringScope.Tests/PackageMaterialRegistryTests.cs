using System.Formats.Tar;
using System.IO.Compression;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class PackageMaterialRegistryTests
{
    [Theory]
    [InlineData("missing")]
    [InlineData("neighbor-only")]
    public void EveryRegisteredBuiltProjectRequiresItsExactReceipt(string defect)
    {
        using var fixture = new Fixture();
        fixture.PrepareProjects();
        const string project = "tools/StrataLint.Cli/StrataLint.Cli.csproj";
        var receipt = Path.Combine(fixture.Root, CommonBuildOutputs.RootPath, project + ".outputs");
        if (defect == "missing") File.Delete(receipt);
        else File.Move(receipt, Path.Combine(fixture.Root, CommonBuildOutputs.RootPath, "neighbor.outputs"));

        var error = Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(fixture.Root));

        Assert.Contains("missing registered build receipt", error.Message, StringComparison.Ordinal);
        Assert.Contains(project, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ExactReceiptCannotDeclareAnotherRegisteredProject()
    {
        using var fixture = new Fixture();
        fixture.PrepareProjects();
        const string project = "tools/StrataLint.Cli/StrataLint.Cli.csproj";
        var receipt = Path.Combine(fixture.Root, CommonBuildOutputs.RootPath, project + ".outputs");
        var lines = File.ReadAllLines(receipt);
        lines[0] = Path.Combine(fixture.Root, CurrentExecutionContractTests.CandidateFixture.First);
        File.WriteAllLines(receipt, lines);

        var error = Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(fixture.Root));

        Assert.Contains("build receipt project mismatch", error.Message, StringComparison.Ordinal);
        Assert.Contains(project, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnregisteredNeighborReceiptCannotExpandTransportedMaterials()
    {
        using var fixture = new Fixture();
        fixture.PrepareProjects();
        var before = CommonBuildOutputs.Collect(fixture.Root);
        fixture.Write("build/neighbor/runtime.dll", "unregistered runtime");
        fixture.Write(CommonBuildOutputs.RootPath + "/neighbor.outputs", string.Join('\n', new[] {
            Path.Combine(fixture.Root, "neighbor/Neighbor.csproj"), Path.Combine(fixture.Root, "build/neighbor/runtime.dll"),
            Path.Combine(fixture.Root, "build/neighbor"), "packages=" + fixture.PackageRoot + "-other", "reference=",
            Path.Combine(fixture.Root, "build/neighbor/runtime.dll") }));

        Assert.Equal(before, CommonBuildOutputs.Collect(fixture.Root));
        Assert.DoesNotContain("build/neighbor/runtime.dll", before);
    }

    [Fact]
    public void CompileFailureProofsDoNotRequireSuccessfulBuildReceipts()
    {
        using var fixture = new Fixture();
        fixture.PrepareProjects();
        var manifest = File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path));
        foreach (var name in new[] { "CompileFailProof", "BannedApiCompileFailProof" })
        {
            var project = $"tools/tests/{name}/{name}.csproj";
            fixture.Write(project, "<Project />");
            manifest = EngineeringRegistrationFixture.Append(manifest,
                new EngineeringProjectFixture(project, name, "compile-fail-proof", false, []));
        }
        fixture.Write(EngineeringRegistrationFixture.Path, manifest);

        Assert.NotEmpty(CommonBuildOutputs.Collect(fixture.Root));
    }

    [Fact]
    public void CollectionAcceptsDifferentProjectPackageSubsets()
    {
        using var fixture = new Fixture();
        fixture.PrepareProjects();
        var paths = CommonBuildOutputs.Collect(fixture.Root);
        Assert.Equal(fixture.ExpectedMaterials, paths.Where(path => path.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal)).Order(StringComparer.Ordinal));
        Assert.Equal(2, CommonExecutionEvidence.Read<BuiltTestProject[]>(fixture.Root, CommonBuildOutputs.TestsPath).Length);
        Assert.Contains(paths, path => path.Contains("/ref/", StringComparison.Ordinal));
    }

    [Fact]
    public void AssetsFileInventoryDoesNotSelectDeclaredMaterial()
    {
        using var fixture = new Fixture();
        fixture.WriteAssets(fixture.AssetsPath, ["alpha/1.0.0", "beta/2.0.0"], emptyInventory: true);
        Assert.Equal(fixture.ExpectedRelative, PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).Select(item => item.Relative));
        File.WriteAllText(fixture.AssetsPath, "not JSON; must never be parsed");
        Assert.Equal(fixture.ExpectedRelative, PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).Select(item => item.Relative));
        File.Delete(fixture.AssetsPath);
        Assert.Equal(fixture.ExpectedRelative, PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).Select(item => item.Relative));
    }

    [Theory]
    [InlineData("alpha/1.0.0/.nupkg.metadata")]
    [InlineData("alpha/1.0.0/alpha.nuspec")]
    [InlineData("alpha/1.0.0/lib/net10.0/alpha.dll")]
    [InlineData("beta/2.0.0/beta.dll")]
    public void EachDeclaredRequiredMaterialMustExist(string missing)
    {
        using var fixture = new Fixture();
        File.Delete(Path.Combine(fixture.PackageRoot, missing));
        var error = Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).ToArray());
        Assert.Contains("material", error.Message, StringComparison.Ordinal);
        Assert.Contains(string.Join('/', missing.Split('/').Take(2)), error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EmptyRequiredGlobIsRejectedEvenWhenOtherMaterialExists()
    {
        using var fixture = new Fixture();
        fixture.WriteAssets(fixture.AssetsPath, ["alpha/1.0.0", "beta/2.0.0"], emptyInventory: true);
        fixture.WriteRegistry("""[{"packagePath":"alpha/1.0.0","include":["alpha.nuspec","missing/*.dll"],"exclude":[]}]""");
        var error = Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).ToArray());
        Assert.Contains("missing/*.dll", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("duplicate-package")]
    [InlineData("conflicting-pattern")]
    [InlineData("duplicate-pattern")]
    [InlineData("invalid-package")]
    [InlineData("invalid-pattern")]
    [InlineData("empty-include")]
    [InlineData("extra-field")]
    [InlineData("duplicate-field")]
    [InlineData("wrong-schema-type")]
    [InlineData("malformed-json")]
    public void ProductionParserRejectsInvalidManifest(string defect)
    {
        using var fixture = new Fixture();
        const string row = """{"packagePath":"alpha/1.0.0","include":["alpha.nuspec"],"exclude":[]}""";
        fixture.WriteRegistry("[" + row + "]");
        var json = File.ReadAllText(fixture.ManifestPath);
        json = defect switch
        {
            "duplicate-package" => json.Replace(row, row + "," + row, StringComparison.Ordinal),
            "conflicting-pattern" => json.Replace("\"exclude\":[]", "\"exclude\":[\"alpha.nuspec\"]", StringComparison.Ordinal),
            "duplicate-pattern" => json.Replace("[\"alpha.nuspec\"]", "[\"alpha.nuspec\",\"alpha.nuspec\"]", StringComparison.Ordinal),
            "invalid-package" => json.Replace("alpha/1.0.0", "../escape", StringComparison.Ordinal),
            "invalid-pattern" => json.Replace("alpha.nuspec", "../*.dll", StringComparison.Ordinal),
            "empty-include" => json.Replace("[\"alpha.nuspec\"]", "[]", StringComparison.Ordinal),
            "extra-field" => json.Replace("\"schemaVersion\":1", "\"extra\":true,\"schemaVersion\":1", StringComparison.Ordinal),
            "duplicate-field" => json.Replace("\"schemaVersion\":1", "\"schemaVersion\":1,\"schemaVersion\":1", StringComparison.Ordinal),
            "wrong-schema-type" => json.Replace("\"schemaVersion\":1", "\"schemaVersion\":\"1\"", StringComparison.Ordinal),
            "malformed-json" => "{",
            _ => throw new ArgumentException(defect),
        };
        File.WriteAllText(fixture.ManifestPath, json);
        Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Load(fixture.Root));
    }

    [Fact]
    public void MissingManifestIsRejected()
    {
        using var fixture = new Fixture();
        File.Delete(fixture.ManifestPath);
        Assert.Throws<InvalidDataException>(() => PackageMaterialRegistry.Load(fixture.Root));
    }

    [Theory]
    [InlineData("")]
    [InlineData("relative/packages")]
    public void ExpansionRequiresAnExplicitAbsoluteProducerRoot(string packageRoot)
    {
        using var fixture = new Fixture();
        Assert.Contains("absolute producer-supplied", Assert.Throws<InvalidDataException>(() =>
            PackageMaterialRegistry.Expand(fixture.Root, packageRoot).ToArray()).Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("relative")]
    [InlineData("conflicting")]
    public void CollectionRejectsMissingOrConflictingProducerRoots(string defect)
    {
        using var fixture = new Fixture();
        fixture.PrepareProjects();
        var receipt = Path.Combine(fixture.Root, CommonBuildOutputs.RootPath, CurrentExecutionContractTests.CandidateFixture.First + ".outputs");
        var lines = File.ReadAllLines(receipt);
        lines[3] = "packages=" + (defect == "missing" ? "" : defect == "relative" ? "packages" : fixture.PackageRoot + "-other");
        File.WriteAllLines(receipt, lines);
        Assert.Contains("NuGetPackageRoot", Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(fixture.Root)).Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryProductionRegistrationRequiresMaterial()
    {
        using var fixture = new Fixture();
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), PackageMaterialRegistry.RelativePath), fixture.ManifestPath, overwrite: true);
        var manifest = PackageMaterialRegistry.Load(fixture.Root);
        foreach (var row in manifest.Packages) fixture.WritePackage(row.PackagePath + "/.nupkg.metadata");
        Assert.Equal(manifest.Packages.Length, PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).Count());
        foreach (var row in manifest.Packages)
        {
            var material = row.PackagePath + "/.nupkg.metadata";
            File.Delete(Path.Combine(fixture.PackageRoot, material));
            Assert.Contains(row.PackagePath, Assert.Throws<InvalidDataException>(() =>
                PackageMaterialRegistry.Expand(fixture.Root, fixture.PackageRoot).ToArray()).Message, StringComparison.Ordinal);
            fixture.WritePackage(material);
        }
    }

    [Fact]
    public void UndeclaredNeighborDoesNotChangeTransportAndArchiveHasNoDuplicateMaterial()
    {
        using var fixture = new Fixture();
        fixture.PrepareProjects(allPackages: true);
        var first = Pack("first");
        fixture.WritePackage("neighbor/9.0.0/neighbor.dll");
        fixture.WritePackage("alpha/1.0.0/archive.nupkg");
        fixture.WritePackage("alpha/1.0.0/symbols.snupkg");
        var second = Pack("second");
        Assert.Equal(first, second);
        Assert.Equal(second.Length, second.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(fixture.ExpectedMaterials, second.Where(path => path.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal)));

        string[] Pack(string name)
        {
            var paths = CommonBuildOutputs.Collect(fixture.Root);
            fixture.Write("build/build.log", "built\n");
            CommonExecutionEvidence.SealBuild(fixture.Root, CommonExecutionEvidence.Candidate(fixture.Root), paths,
                CommonExecutionEvidence.BuildSteps.Select(step => new StageStep(step, 0, 0, "executed", "build/build.log")).ToArray());
            var archive = Path.Combine(fixture.Root, "build/" + name + ".tgz");
            using var output = new StringWriter();
            Assert.Equal(0, Program.Run(["transport-pack", "--repository", fixture.Root, "--stage", "build", "--commit",
                SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD"), "--run-id", "17", "--run-attempt", "2", "--archive", archive],
                TestResultEvidence.Load, output, output));
            using var stream = File.OpenRead(archive);
            using var gzip = new GZipStream(stream, CompressionMode.Decompress);
            using var tar = new TarReader(gzip);
            var entries = new List<string>();
            while (tar.GetNextEntry() is { } entry) entries.Add(entry.Name);
            return entries.Order(StringComparer.Ordinal).ToArray();
        }
    }

    private sealed class Fixture : IDisposable
    {
        private readonly CurrentExecutionContractTests.CandidateFixture candidate = new();
        internal string Root => candidate.Root;
        internal string PackageRoot => Path.Combine(Root, "build/producer-packages");
        internal string AssetsPath => Path.Combine(Root, "build/project.assets.json");
        internal string ManifestPath => Path.Combine(Root, PackageMaterialRegistry.RelativePath);
        internal string[] ExpectedRelative { get; } = ["alpha/1.0.0/.nupkg.metadata", "alpha/1.0.0/alpha.nuspec", "alpha/1.0.0/lib/net10.0/alpha.dll", "beta/2.0.0/beta.dll"];
        internal string[] ExpectedMaterials => ExpectedRelative.Select(path => CommonBuildOutputs.PackagesPath + "/" + path).ToArray();

        internal Fixture()
        {
            Write(".gitignore", ".lake/\nbuild/\n**/bin/\n**/obj/\n");
            WriteRegistry("""
                [{"packagePath":"alpha/1.0.0","include":["**/*",".nupkg.metadata","alpha.nuspec","lib/**/*.dll"],"exclude":["**/*.nupkg","**/*.snupkg"]},
                 {"packagePath":"beta/2.0.0","include":["beta.dll"],"exclude":[]}]
                """);
            foreach (var path in ExpectedRelative) WritePackage(path);
            WriteAssets(AssetsPath, ["alpha/1.0.0", "beta/2.0.0"]);
        }

        internal void PrepareProjects(bool allPackages = false)
        {
            var repository = TestRepositoryLayout.FindRoot();
            var registrations = new List<EngineeringProjectFixture>();
            foreach (var assembly in new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.RunnerPath,
                         CommonExecutionEvidence.LeanProducerPath, CommonExecutionEvidence.ScribePath })
            {
                var directory = assembly[..assembly.IndexOf("/bin/", StringComparison.Ordinal)];
                Project(directory + "/" + Path.GetFileName(directory) + ".csproj", assembly, Path.Combine(repository, assembly), false);
            }
            foreach (var project in new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second })
                Project(project, Path.GetDirectoryName(project) + "/bin/Release/net10.0/" + Path.GetFileName(typeof(PackageMaterialRegistryTests).Assembly.Location),
                    typeof(PackageMaterialRegistryTests).Assembly.Location, true);
            Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(registrations.ToArray()));
            SharedBuildContractTests.Git(Root, "add", ".");
            SharedBuildContractTests.Git(Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "package collection fixture");

            void Project(string project, string assembly, string source, bool test)
            {
                Write(project, $"<Project><PropertyGroup><IsTestProject>{test.ToString().ToLowerInvariant()}</IsTestProject></PropertyGroup></Project>\n");
                registrations.Add(new EngineeringProjectFixture(project, Path.GetFileNameWithoutExtension(assembly),
                    test ? "cross-cutting-test" : "production", test, [], OwnedTestAssembly: test ? null : "Fixture.Tests"));
                var full = Path.Combine(Root, assembly);
                Directory.CreateDirectory(Path.GetDirectoryName(full)!);
                File.Copy(source, full);
                Write(Path.ChangeExtension(assembly, ".deps.json"), "{}");
                Write(Path.ChangeExtension(assembly, ".runtimeconfig.json"), "{}");
                var reference = Path.Combine(Root, Path.GetDirectoryName(project)!, "obj/ref", Path.GetFileName(assembly));
                Directory.CreateDirectory(Path.GetDirectoryName(reference)!);
                File.Copy(source, reference);
                var assets = Path.Combine(Root, Path.GetDirectoryName(project)!, "obj/project.assets.json");
                WriteAssets(assets, allPackages ? ["alpha/1.0.0", "beta/2.0.0"] : test ? ["beta/2.0.0"] : ["alpha/1.0.0"]);
                Write(CommonBuildOutputs.RootPath + "/" + project + ".outputs", string.Join('\n',
                    new[] { Path.Combine(Root, project), full, Path.GetDirectoryName(full)!, "packages=" + PackageRoot, "reference=" + reference,
                        full, Path.ChangeExtension(full, ".deps.json"), Path.ChangeExtension(full, ".runtimeconfig.json"), reference }) + "\n");
            }
        }

        internal void WriteRegistry(string packages) => Write(PackageMaterialRegistry.RelativePath,
            "{\"schemaVersion\":1,\"packageRootSource\":\"build-output:NuGetPackageRoot\",\"packages\":" + packages + "}");
        internal void WritePackage(string path) => Write("build/producer-packages/" + path, "fixture:" + path);
        internal void WriteAssets(string path, string[] packages, bool emptyInventory = false)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, JsonSerializer.Serialize(new {
                packageFolders = new Dictionary<string, object> { [PackageRoot] = new { } },
                libraries = packages.ToDictionary(package => package, package => new {
                    type = "package", path = package, files = emptyInventory ? [] : ExpectedRelative
                        .Where(file => file.StartsWith(package + "/", StringComparison.Ordinal)).Select(file => file[(package.Length + 1)..]).ToArray() }) }));
        }
        internal void Write(string path, string text)
        {
            var full = Path.Combine(Root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, text);
        }
        public void Dispose() => candidate.Dispose();
    }
}

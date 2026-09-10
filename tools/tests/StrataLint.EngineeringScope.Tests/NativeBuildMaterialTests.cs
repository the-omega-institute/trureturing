using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.EngineeringScope.Tests;

public sealed class NativeBuildMaterialTests(ITestOutputHelper output)
{
    [Fact]
    public void NativeSelectionRelocatesTransitiveRuntimeAndRejectsMissingOrCorruptAssets()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new NativeMaterialFixture(output);
        var root = fixture.Root;
        var physicalRoot = SharedBuildContractTests.Git(root, "rev-parse", "--show-toplevel");
        var paths = CommonBuildOutputs.Collect(physicalRoot);
        output.WriteLine("MATERIAL_BEFORE_SAME_FIXTURE " + JsonSerializer.Serialize(fixture.FullInventory()));
        output.WriteLine("MATERIAL_MEASUREMENT " + JsonSerializer.Serialize(new {
            files = paths.Length, bytes = paths.Sum(path => new FileInfo(Path.Combine(root, path)).Length),
            package_files = paths.Count(path => path.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal)),
            package_bytes = paths.Where(path => path.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal))
                .Sum(path => new FileInfo(Path.Combine(root, path)).Length) }));
        Assert.DoesNotContain(paths, path => path.EndsWith("/unused-payload.bin", StringComparison.Ordinal));
        Assert.DoesNotContain(paths, path => path.Contains("/lib/net9.0/", StringComparison.Ordinal));
        Assert.DoesNotContain(paths, path => path.StartsWith("tools/tests/StrataLint.ScriptTests/bin/", StringComparison.Ordinal));
        Assert.Contains(paths, path => path.EndsWith("/lib/net10.0/Inner.dll", StringComparison.Ordinal));
        Assert.Contains(paths, path => path.EndsWith("/lib/net10.0/fr/Inner.resources.dll", StringComparison.Ordinal));
        Assert.Contains(paths, path => path.EndsWith("/runtimes/linux-x64/native/fixture.so", StringComparison.Ordinal));
        Assert.Contains(paths, path => path.EndsWith("/runtimes/osx-arm64/native/fixture.dylib", StringComparison.Ordinal));
        Assert.Contains(paths, path => path.EndsWith("/build-input.bin", StringComparison.Ordinal));
        Assert.Contains(paths, path => path.EndsWith("/ref/StrataLint.dll", StringComparison.Ordinal));

        var build = CommonExecutionEvidence.ValidateBuild(root);
        using var consumer = new CurrentExecutionContractTests.CandidateFixture();
        // Only tracked candidate source and the sealed material list reach the recipient.
        foreach (var path in SharedBuildContractTests.Git(root, "ls-files").Split('\n'))
            Copy(path);
        foreach (var path in build.Materials.Select(material => material.Path).Append(CommonExecutionEvidence.BuildPath)) Copy(path);
        foreach (var path in new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second })
            TemporaryFileSystem.File.Delete(Path.Combine(consumer.Root, path));
        SharedBuildContractTests.Git(consumer.Root, "add", ".");
        var offline = root + "-offline";
        Directory.Move(root, offline);
        try
        {
            var received = CommonExecutionEvidence.ValidateBuild(consumer.Root);
            var packages = Path.Combine(consumer.Root, CommonBuildOutputs.PackagesPath);
            var environment = new Dictionary<string, string> { ["NUGET_PACKAGES"] = packages };
            var app = SharedBuildContractTests.Process(consumer.Root, "dotnet", [CommonExecutionEvidence.CliPath], environment);
            Assert.True(app.Exit == 0, app.Text);
            Assert.Contains("bonjour", app.Text, StringComparison.Ordinal);
            var appDirectory = Path.GetDirectoryName(Path.Combine(consumer.Root, CommonExecutionEvidence.CliPath))!;
            var localCopies = new[] { "Outer.dll", "Inner.dll", "fr/Inner.resources.dll" }
                .ToDictionary(name => Path.Combine(appDirectory, name), name => File.ReadAllBytes(Path.Combine(appDirectory, name)));
            try
            {
                foreach (var path in localCopies.Keys) TemporaryFileSystem.File.Delete(path);
                var probing = SharedBuildContractTests.Process(consumer.Root, "dotnet",
                    ["exec", "--additionalprobingpath", packages, CommonExecutionEvidence.CliPath], environment);
                Assert.True(probing.Exit == 0, probing.Text);
                Assert.Contains("bonjour", probing.Text, StringComparison.Ordinal);
            }
            finally { foreach (var (path, bytes) in localCopies) TemporaryFileSystem.File.WriteAllBytes(path, bytes); }
            var tests = CommonBuildOutputs.TestAssemblies(consumer.Root, received);
            Assert.Equal(NativeMaterialFixture.TestProject, Assert.Single(tests).Key);
            var results = Path.Combine(consumer.Root, "build/runtime-results");
            var run = SharedBuildContractTests.Process(consumer.Root, "dotnet",
                Program.BuildTestArguments(tests[NativeMaterialFixture.TestProject], results).ToArray(), environment);
            output.WriteLine(run.Text);
            Assert.True(run.Exit == 0, run.Text);
            Assert.True(TestResultEvidence.Load(results).Executed > 0);
            // Retain the nested raw TRX with the outer result, before scratch cleanup.
            foreach (var trx in Directory.GetFiles(results, "*.trx", SearchOption.AllDirectories))
                output.WriteLine("NESTED_TRX " + Convert.ToBase64String(File.ReadAllBytes(trx)));
            Assert.Empty(Directory.GetFiles(consumer.Root, "project.assets.json", SearchOption.AllDirectories));
            var restore = SharedBuildContractTests.Process(consumer.Root, "dotnet",
                ["restore", NativeMaterialFixture.ProofProject, "--locked-mode", "--packages", packages], environment);
            Assert.True(restore.Exit == 0, restore.Text);
            var proof = SharedBuildContractTests.Process(consumer.Root, "dotnet",
                ["build", NativeMaterialFixture.ProofProject, "--configuration", "Release", "--no-restore", "--no-dependencies"], environment);
            Assert.True(CompilationProof.ValidateCapability(proof.Exit, proof.Text), proof.Text);
            output.WriteLine("RELOCATED_LOCKED_RESTORE exit=" + restore.Exit + "\nRELOCATED_NEGATIVE_PROOF exit=" + proof.Exit + "\n" + proof.Text);
            foreach (var suffix in new[] { "/lib/net10.0/Inner.dll", "/lib/net10.0/fr/Inner.resources.dll",
                         "/runtimes/linux-x64/native/fixture.so" })
            {
                var material = Assert.Single(received.Materials, material => material.Path.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal)
                    && material.Path.EndsWith(suffix, StringComparison.Ordinal));
                var path = Path.Combine(consumer.Root, material.Path);
                var bytes = File.ReadAllBytes(path);
                TemporaryFileSystem.File.Delete(path);
                Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.ValidateBuild(consumer.Root));
                TemporaryFileSystem.File.WriteAllText(path, "corrupt runtime");
                Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateBuild(consumer.Root));
                TemporaryFileSystem.File.WriteAllBytes(path, bytes);
            }
            CommonExecutionEvidence.ValidateBuild(consumer.Root);
        }
        finally { Directory.Move(offline, root); }

        // Missing native inputs at the producer cannot become a smaller successful inventory.
        var runtimeSource = Path.Combine(root, "build/packages/inner/1.0.0/lib/net10.0/Inner.dll");
        var runtimeBytes = File.ReadAllBytes(runtimeSource);
        TemporaryFileSystem.File.Delete(runtimeSource);
        Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(physicalRoot));
        TemporaryFileSystem.File.WriteAllBytes(runtimeSource, runtimeBytes);

        void Copy(string relative)
        {
            var target = Path.Combine(consumer.Root, relative);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            TemporaryFileSystem.File.WriteAllBytes(target, File.ReadAllBytes(Path.Combine(root, relative)));
        }
    }

    [Fact]
    public void UnknownPackageInputsStayWholeAndUnresolvedDependenciesCannotBeDropped()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new NativeMaterialFixture(output);
        var root = fixture.Root;
        var physical = SharedBuildContractTests.Git(root, "rev-parse", "--show-toplevel");
        Assert.Contains(CommonBuildOutputs.PackagesPath + "/xunit.assert/2.9.3/.signature.p7s", CommonBuildOutputs.Collect(physical));
        var path = Path.Combine(root, "tools/StrataLint.Cli/obj/project.assets.json");
        var original = File.ReadAllText(path);
        var depsPath = Path.Combine(root, Path.ChangeExtension(CommonExecutionEvidence.CliPath, ".deps.json"));
        var originalDeps = File.ReadAllText(depsPath);
        var deps = JsonNode.Parse(originalDeps)!;
        deps["targets"]!.AsObject().First().Value!["Inner/1.0.0"]!["runtime"]!["lib/net10.0/unresolved.dll"] = new JsonObject();
        TemporaryFileSystem.File.WriteAllText(depsPath, deps.ToJsonString());
        Assert.Contains("asset is absent", Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(physical)).Message, StringComparison.Ordinal);
        TemporaryFileSystem.File.WriteAllText(depsPath, originalDeps);
        var assets = JsonNode.Parse(original)!;
        var target = assets["targets"]!.AsObject().First().Value!;
        target["Inner/1.0.0"]!["compile"]!["lib/net9.0/_._"] = new JsonObject();
        TemporaryFileSystem.File.WriteAllText(path, assets.ToJsonString());
        Assert.DoesNotContain(CommonBuildOutputs.Collect(physical), path => path.EndsWith("/lib/net9.0/_._", StringComparison.Ordinal));
        target["Outer/1.0.0"]!["futureBuildInputs"] = new JsonObject();
        TemporaryFileSystem.File.WriteAllText(path, assets.ToJsonString());
        Assert.Contains(CommonBuildOutputs.Collect(physical), path => path.EndsWith("/unused-payload.bin", StringComparison.Ordinal));
        target["Outer/1.0.0"]!.AsObject().Remove("futureBuildInputs");
        target["Outer/1.0.0"]!["dependencies"]!["Unresolved"] = "1.0.0";
        TemporaryFileSystem.File.WriteAllText(path, assets.ToJsonString());
        Assert.Contains("unresolved package dependency", Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(physical)).Message, StringComparison.Ordinal);
        TemporaryFileSystem.File.WriteAllText(path, original);

        // An excluded test is still required when native project ownership makes
        // it a dependency of an executed consumer (including build-only references).
        var manifest = Path.Combine(root, CommonBuildOutputs.RootPath, "tools/StrataLint.Cli/StrataLint.Cli.csproj.outputs");
        TemporaryFileSystem.File.AppendAllText(manifest, "project=" + Path.Combine(physical,
            "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj") + "\n");
        Assert.Contains(CommonBuildOutputs.Collect(physical), path => path.StartsWith("tools/tests/StrataLint.ScriptTests/bin/", StringComparison.Ordinal));
        TemporaryFileSystem.File.AppendAllText(manifest, "project=" + Path.Combine(physical, "tools/Missing/Missing.csproj") + "\n");
        Assert.Contains("required project was not built", Assert.Throws<InvalidDataException>(() => CommonBuildOutputs.Collect(physical)).Message, StringComparison.Ordinal);
    }
}

internal sealed class NativeMaterialFixture : IDisposable
{
    internal const string TestProject = "tools/tests/Runtime/Runtime.csproj";
    internal const string ProofProject = "tools/tests/CompileFailProof/CompileFailProof.csproj";
    private readonly CurrentExecutionContractTests.CandidateFixture candidate = new();
    internal string Root => candidate.Root;

    internal NativeMaterialFixture(ITestOutputHelper output)
    {
        var repository = TestRepositoryLayout.FindRoot();
        foreach (var path in new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second })
            TemporaryFileSystem.File.Delete(Path.Combine(Root, path));
        Write(".gitignore", "build/\n**/bin/\n**/obj/\n");
        Write("global.json", File.ReadAllText(Path.Combine(repository, "global.json")));
        Write("tools/scripts/ci-build-outputs.targets", File.ReadAllText(Path.Combine(repository, "tools/scripts/ci-build-outputs.targets")));
        Write("NuGet.Config", "<configuration><packageSources><clear /><add key=\"fixture\" value=\"build/feed\" /></packageSources><fallbackPackageFolders><clear /></fallbackPackageFolders></configuration>");
        Write("build/Inner/Inner.csproj", """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Version>1.0.0</Version></PropertyGroup>
            <ItemGroup><None Include="unused-payload.bin" Pack="true" PackagePath="docs/" />
            <None Include="bin/Release/net10.0/Inner.dll" Pack="true" PackagePath="lib/net9.0/" />
            <None Include="fixture.so" Pack="true" PackagePath="runtimes/linux-x64/native/" />
            <None Include="fixture.dylib" Pack="true" PackagePath="runtimes/osx-arm64/native/" /></ItemGroup></Project>
            """);
        Write("build/Inner/Value.cs", """
            public static class InnerValue {
                public static string Read() => new System.Resources.ResourceManager("Inner.Greeting", typeof(InnerValue).Assembly)
                    .GetString("Value", System.Globalization.CultureInfo.GetCultureInfo("fr"));
            }
            """);
        foreach (var (name, value) in new[] { ("Greeting", "hello"), ("Greeting.fr", "bonjour") })
            Write("build/Inner/" + name + ".resx", $"<root><resheader name=\"resmimetype\"><value>text/microsoft-resx</value></resheader><data name=\"Value\" xml:space=\"preserve\"><value>{value}</value></data></root>");
        Write("build/Inner/unused-payload.bin", new string('x', 131072));
        Write("build/Inner/fixture.so", "declared Linux native asset\n");
        Write("build/Inner/fixture.dylib", "declared macOS native asset\n");
        Write("build/Outer/Outer.csproj", """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Version>1.0.0</Version></PropertyGroup>
            <ItemGroup><ProjectReference Include="../Inner/Inner.csproj" /></ItemGroup></Project>
            """);
        Write("build/Outer/Value.cs", "public static class OuterValue { public static string Read() => InnerValue.Read(); }");
        // Package targets may read arbitrary sibling payloads; that package stays whole.
        Write("build/BuildInput/BuildInput.csproj", """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Version>1.0.0</Version></PropertyGroup>
            <ItemGroup><None Include="BuildInput.targets" Pack="true" PackagePath="build/" />
            <None Include="build-input.bin" Pack="true" PackagePath="payload/" /></ItemGroup></Project>
            """);
        Write("build/BuildInput/BuildInput.targets", "<Project><Target Name=\"ReadFixtureBuildInput\" BeforeTargets=\"CoreCompile\"><ReadLinesFromFile File=\"$(MSBuildThisFileDirectory)../payload/build-input.bin\" /></Target></Project>");
        Write("build/BuildInput/build-input.bin", "required by package target\n");
        foreach (var package in new[] { "Inner", "Outer", "BuildInput" })
            Run("dotnet", "pack", $"build/{package}/{package}.csproj", "--configuration", "Release", "--output", "build/feed");

        foreach (var (project, assembly) in new[] { ("StrataLint.Cli", "StrataLint"),
                     ("StrataLint.EngineeringScope", "StrataLint.EngineeringScope"), ("StrataLint.Scribe.Documents", "StrataLint.Scribe.Documents") })
        {
            Write($"tools/{project}/{project}.csproj", $"""
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><OutputType>Exe</OutputType>
                <AssemblyName>{assembly}</AssemblyName><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup>
                <ItemGroup><PackageReference Include="Outer" Version="1.0.0" /><PackageReference Include="BuildInput" Version="1.0.0" /></ItemGroup></Project>
                """);
            Write($"tools/{project}/Program.cs", "System.Console.WriteLine(OuterValue.Read());");
        }
        Write(TestProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject>
            <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup><ItemGroup>
            <PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" /><PackageReference Include="xunit" Version="2.9.3" />
            <PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" /><PackageReference Include="Outer" Version="1.0.0" />
            </ItemGroup></Project>
            """);
        Write("tools/tests/Runtime/RuntimeTests.cs", "public class RuntimeTests { [Xunit.Fact] public void TransitiveResourceRuns() => Xunit.Assert.Equal(\"bonjour\", OuterValue.Read()); }");
        Write(ProofProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>false</IsTestProject>
            <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup><ItemGroup>
            <PackageReference Include="BuildInput" Version="1.0.0" /><PackageReference Include="Outer" Version="1.0.0" /></ItemGroup></Project>
            """);
        Write("tools/tests/CompileFailProof/MissingCapability.cs", "public class MissingCapability { void Check() => Require(); void Require(int metaClear) {} }");
        const string excluded = "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
        Write(excluded, "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>");
        Write("tools/tests/StrataLint.ScriptTests/Excluded.cs", "public class Excluded { }");
        Run("dotnet", "new", "sln", "--name", "StrataLint", "--format", "sln", "--output", "tools");
        Run("dotnet", "sln", "tools/StrataLint.sln", "add", TestProject, excluded,
            "tools/StrataLint.Cli/StrataLint.Cli.csproj", "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            "tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj");
        // Shared engineering receives selected packages and tracked source, without
        // the owning project's obj. Local runs ask NuGet for its configured root;
        // an explicit recipient NUGET_PACKAGES never falls back to another root.
        var packageSource = Environment.GetEnvironmentVariable("NUGET_PACKAGES");
        if (packageSource is null)
        {
            var query = SharedBuildContractTests.Process(repository, "dotnet", ["nuget", "locals", "global-packages", "--list"],
                new Dictionary<string, string> { ["DOTNET_CLI_UI_LANGUAGE"] = "en-US" });
            Assert.True(query.Exit == 0, query.Text);
            Assert.StartsWith("global-packages: ", query.Text, StringComparison.Ordinal);
            packageSource = query.Text["global-packages: ".Length..].Trim();
            output.WriteLine("FIXTURE_NUGET_SOURCE local-nuget=" + packageSource);
        }
        else output.WriteLine("FIXTURE_NUGET_SOURCE NUGET_PACKAGES=" + packageSource);
        Assert.True(Path.IsPathFullyQualified(packageSource), "fixture requires an absolute NuGet package root: " + packageSource);
        using var locked = JsonDocument.Parse(File.ReadAllText(Path.Combine(repository, "tools/tests/StrataLint.EngineeringScope.Tests/packages.lock.json")));
        foreach (var library in locked.RootElement.GetProperty("dependencies").EnumerateObject()
                     .SelectMany(framework => framework.Value.EnumerateObject()))
        {
            if (library.Value.GetProperty("type").GetString() == "Project") continue;
            var path = library.Name.ToLowerInvariant() + "/" + library.Value.GetProperty("resolved").GetString()!.ToLowerInvariant();
            var source = Path.Combine(packageSource, path);
            foreach (var file in Directory.GetFiles(source, "*", SearchOption.AllDirectories))
            {
                var target = Path.Combine(Root, "build/packages", path, Path.GetRelativePath(source, file));
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                TemporaryFileSystem.File.WriteAllBytes(target, File.ReadAllBytes(file));
            }
        }
        Run("dotnet", "restore", "tools/StrataLint.sln", "--packages", Path.Combine(Root, "build/packages"), "--use-lock-file");
        Run("dotnet", "restore", ProofProject, "--packages", Path.Combine(Root, "build/packages"), "--use-lock-file");
        SharedBuildContractTests.Git(Root, "add", ".");
        var physical = SharedBuildContractTests.Git(Root, "rev-parse", "--show-toplevel");
        var build = SharedBuildContractTests.Process(Root, "dotnet",
            [typeof(Program).Assembly.Location, "build", "--repository", physical],
            new Dictionary<string, string> { ["NUGET_PACKAGES"] = Path.Combine(physical, "build/packages") });
        Assert.True(build.Exit == 0, build.Text);
    }

    internal void Write(string path, string text)
    {
        var full = Path.Combine(Root, path);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        TemporaryFileSystem.File.WriteAllText(full, text);
    }

    // Measurement of the former producer's complete FileWrites/package inventory
    // against these same physical files, without a second build or package download.
    internal object FullInventory()
    {
        var files = new Dictionary<string, long>(StringComparer.Ordinal);
        foreach (var manifest in Directory.GetFiles(Path.Combine(Root, CommonBuildOutputs.RootPath), "*.outputs", SearchOption.AllDirectories))
        {
            var lines = File.ReadAllLines(manifest);
            foreach (var path in lines.Skip(5).Where(Path.IsPathRooted)
                         .Where(path => path.StartsWith(lines[2], StringComparison.Ordinal) || path == lines[4][10..]))
                files[path] = new FileInfo(path).Length;
            using var assets = JsonDocument.Parse(File.ReadAllText(lines[3]));
            var folders = assets.RootElement.GetProperty("packageFolders").EnumerateObject().Select(item => item.Name).ToArray();
            foreach (var library in assets.RootElement.GetProperty("libraries").EnumerateObject())
            {
                if (library.Value.GetProperty("type").GetString() != "package") continue;
                foreach (var file in library.Value.GetProperty("files").EnumerateArray())
                {
                    var relative = library.Value.GetProperty("path").GetString() + "/" + file.GetString();
                    files[CommonBuildOutputs.PackagesPath + "/" + relative] = new FileInfo(
                        folders.Select(folder => Path.Combine(folder, relative)).First(File.Exists)).Length;
                }
            }
        }
        files[CommonBuildOutputs.TestsPath] = new FileInfo(Path.Combine(Root, CommonBuildOutputs.TestsPath)).Length;
        return new { files = files.Count, bytes = files.Values.Sum(),
            package_files = files.Count(pair => pair.Key.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal)),
            package_bytes = files.Where(pair => pair.Key.StartsWith(CommonBuildOutputs.PackagesPath + "/", StringComparison.Ordinal)).Sum(pair => pair.Value) };
    }

    private void Run(string executable, params string[] arguments)
    {
        var result = SharedBuildContractTests.Process(Root, executable, arguments,
            new Dictionary<string, string> { ["NUGET_PACKAGES"] = Path.Combine(Root, "build/packages") });
        Assert.True(result.Exit == 0, result.Text);
    }

    public void Dispose() => candidate.Dispose();
}

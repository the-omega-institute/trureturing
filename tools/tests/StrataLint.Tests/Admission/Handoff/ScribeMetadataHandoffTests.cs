using Microsoft.CodeAnalysis;
using System.Text;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

public sealed class ScribeMetadataHandoffTests
{
    [Theory]
    [InlineData("transport")]
    [InlineData("missing-manifest")]
    [InlineData("unbound-manifest")]
    [InlineData("missing-reference")]
    [InlineData("corrupt-reference")]
    [InlineData("unbound-reference")]
    public void TransportedClosureRunsRealAnalysisAndRejectsIncompleteEvidence(string scenario)
    {
        var producer = Directory.CreateTempSubdirectory("metadata-producer-").FullName;
        var recipient = Directory.CreateTempSubdirectory("metadata-recipient-").FullName;
        try
        {
            foreach (var file in Snapshot(true).Files.Values)
            {
                var destination = Path.Combine(producer, file.Path.Value);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.WriteAllBytes(destination, file.RawBytes.ToArray());
            }
            File.WriteAllText(Path.Combine(producer, ".gitignore"), "build/\n**/obj/\n**/bin/\n");
            Git(producer, "init", "-q");
            Git(producer, "add", ".");
            Git(producer, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "candidate");
            var snapshot = CommonExecutionEvidence.Snapshot(producer);
            Assert.Equal(0, StrataLint.EngineeringScope.Program.RunCurrentTests(producer, (_, results) =>
            {
                File.WriteAllText(Path.Combine(results, "execution.trx"), """
                    <TestRun><Results><UnitTestResult testId="one" testName="Existing.Runs" outcome="Passed" /></Results>
                    <TestDefinitions><UnitTest id="one" storage="Probe.dll"><TestMethod className="Existing" name="Runs" /></UnitTest></TestDefinitions>
                    <ResultSummary outcome="Completed"><Counters executed="1" passed="1" failed="0" /></ResultSummary></TestRun>
                    """);
                return 0;
            }, TextWriter.Null));
            const string log = "build/ci/fixture.log";
            File.WriteAllText(Path.Combine(producer, log), "executed\n");
            var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(producer, CommonExecutionEvidence.TestsPath).Candidate;
            CommonExecutionEvidence.SealEngineering(producer, candidate, [], CommonExecutionEvidence.EngineeringSteps
                .Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
            var materials = CommonExecutionEvidence.ValidateEngineering(producer).Materials;
            Assert.Contains(materials, item => item.Path.EndsWith("/xunit.core.dll", StringComparison.Ordinal));
            var commit = Git(producer, "rev-parse", "HEAD");
            var archive = Path.Combine(producer, "build", "engineering.tar.gz");
            Assert.Equal(0, Transport("transport-pack", producer, commit, archive));
            Git(producer, "clone", "--quiet", "--no-hardlinks", producer, recipient);
            Assert.False(Directory.Exists(Path.Combine(recipient, "build/ci")));
            var extraction = TestProcessRunner.Run("python3", ["-c",
                    "import pathlib, sys; sys.path.insert(0, sys.argv[1]); import ci; ci.extract(pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3]))",
                    Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow"), recipient, archive],
                producer, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            Assert.True(extraction.ExitCode == 0, Encoding.UTF8.GetString(extraction.StandardError));
            Directory.Delete(producer, recursive: true);
            Assert.Equal(0, Transport("transport-verify", recipient, commit));
            Assert.Equal(materials, CommonExecutionEvidence.ValidateEngineering(recipient).Materials);
            Assert.False(Directory.Exists(Path.Combine(recipient, "obj")));
            Assert.False(Directory.Exists(Path.Combine(recipient, "bin")));
            Assert.False(Directory.Exists(Path.Combine(recipient, ".nuget")));
            Assert.False(Directory.Exists(Path.Combine(recipient, "build/ci/nuget")));
            var reference = materials.First(item => item.Path.EndsWith("/xunit.core.dll", StringComparison.Ordinal));
            switch (scenario)
            {
                case "missing-manifest": File.Delete(Path.Combine(recipient, CommonCompileMetadata.ManifestPath)); break;
                case "unbound-manifest": materials = materials.Where(item => item.Path != CommonCompileMetadata.ManifestPath).ToArray(); break;
                case "missing-reference": File.Delete(Path.Combine(recipient, reference.Path)); break;
                case "corrupt-reference": File.WriteAllText(Path.Combine(recipient, reference.Path), "corrupt metadata"); break;
                case "unbound-reference": materials = materials.Where(item => item != reference).ToArray(); break;
            }
            if (scenario != "transport")
            {
                if (scenario.StartsWith("missing-", StringComparison.Ordinal))
                    Assert.ThrowsAny<IOException>(() => CommonCompileMetadata.Load(recipient, materials));
                else
                    Assert.Throws<InvalidDataException>(() => CommonCompileMetadata.Load(recipient, materials));
                return;
            }
            var inputs = CommonCompileMetadata.Load(recipient, materials);
            var platform = ScribeMetadataReferenceResolver.PlatformReferences()
                .Cast<PortableExecutableReference>().Select(reference => reference.FilePath!).ToHashSet(StringComparer.Ordinal);
            foreach (var path in inputs(ScribeProjectCompilationContext.Create(snapshot.Files.Values
                         .Select(file => new ScribeTrackedSource(file.Path.Value, file.Text)).ToArray(),
                         new Dictionary<string, string>(), new HashSet<string>()).Projects))
                Assert.True(platform.Contains(path) || path.StartsWith(Path.Combine(recipient, "build/ci/compile-metadata/packages")
                    + Path.DirectorySeparatorChar, StringComparison.Ordinal), path);
            var calls = new List<string>();
            ProcessOutput Evaluate(string host, IEnumerable<string> arguments, string root, TimeSpan timeout,
                int limit, ReadOnlyMemory<byte> stdin, IReadOnlyDictionary<string, string>? environment)
            {
                Assert.Equal("msbuild", arguments.First());
                Assert.Contains("-getItem:Compile", arguments);
                Assert.DoesNotContain(arguments, argument => argument.StartsWith("-target:", StringComparison.Ordinal));
                calls.Add(arguments.ElementAt(1));
                return TestProcessRunner.Classify(() => BoundedProcessRunner.Run(host, arguments, root, timeout,
                    limit, stdin, environment), host);
            }
            ScribeTestMap Derive(RepositorySnapshot source) => ScribeTestMapDeriver.DeriveSnapshot(source, inputs,
                data => ScribeTestMapDeriver.DeriveSnapshotUncached(data, Evaluate, inputs));
            var current = Derive(snapshot);
            var baseline = Derive(Snapshot(false));
            Assert.Equal(6, calls.Count);
            Assert.Empty(current.CompileQueryFindings);
            Assert.Empty(baseline.CompileQueryFindings);
            Assert.Equal(2, current.Methods.Count);
            Assert.Single(baseline.Methods);
            Assert.All(current.Methods, method => Assert.Empty(method.UnknownReasons));
            Assert.Empty(ScribeUnknownDebtPolicy.Evaluate(current, baseline));
            Assert.Throws<InvalidDataException>(() => Derive(Snapshot(true, "0.0.0-not-transported")));
        }
        finally
        {
            if (Directory.Exists(producer)) Directory.Delete(producer, recursive: true);
            Directory.Delete(recipient, recursive: true);
        }
    }

    private static int Transport(string command, string root, string commit, string? archive = null) =>
        CiTransport.Run(new[] { command, "--repository", root, "--stage", "engineering", "--commit", commit,
                "--run-id", "17", "--run-attempt", "2" }
            .Concat(archive is null ? [] : new[] { "--archive", archive }).ToArray(), TextWriter.Null);

    private static string Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    [Fact]
    public void ProducerWithAbsentMetadataFailsExplicitly()
    {
        var root = Directory.CreateTempSubdirectory("metadata-absent-").FullName;
        try
        {
            var failure = Assert.Throws<InvalidDataException>(() => CommonCompileMetadata.Export(root,
                Snapshot(true), (id, version) => Path.Combine(root, "empty-packages", id, version)));
            Assert.Contains("compile metadata package is unavailable", failure.Message, StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(root, CommonCompileMetadata.ManifestPath)));
        }
        finally { Directory.Delete(root, recursive: true); }
    }

    [Fact]
    public void SuppliedMetadataIsUsedByActualSnapshotCompilation()
    {
        var snapshot = Snapshot(true, "0.0.0-unavailable-metadata-fixture");
        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot, _ => References());

        Assert.Empty(map.CompileQueryFindings);
        Assert.Equal(2, map.Methods.Count);
        Assert.All(map.Methods, method => Assert.Empty(method.UnknownReasons));
        Assert.Empty(ScribeUnknownDebtPolicy.Evaluate(map,
            ScribeTestMapDeriver.DeriveSnapshot(Snapshot(false, "0.0.0-unavailable-metadata-fixture"), _ => References())));
    }

    private static string[] References() => ScribeMetadataReferenceResolver.PlatformReferences()
        .Cast<PortableExecutableReference>().Select(reference => reference.FilePath!)
        .Concat(new[] { typeof(Xunit.FactAttribute).Assembly.Location, typeof(Xunit.Assert).Assembly.Location,
            typeof(Xunit.Abstractions.ITest).Assembly.Location }).ToArray();

    internal static RepositorySnapshot Snapshot(bool addition, string version = "2.9.3")
    {
        var files = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText("tools/tests/Probe/Probe.csproj", """
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>
                <ItemGroup><PackageReference Include="xunit" /></ItemGroup></Project>
                """),
            RawRepositoryEntry.FromText("tools/tests/Probe/packages.lock.json", $$$$$"""
                {"dependencies":{"net10.0":{"xunit.extensibility.core":{"resolved":"{{{{{version}}}}}"},
                "xunit.assert":{"resolved":"{{{{{version}}}}}"},"xunit.abstractions":{"resolved":"2.0.3"}}}}
                """),
            RawRepositoryEntry.FromText("tools/tests/Probe/Existing.cs",
                "public class Existing { [Xunit.Fact] public void Runs() { Xunit.Assert.True(true); } }"),
        };
        foreach (var path in ScribeTestMapDeriver.CompileFailProofProjectExemptions)
            files.Add(RawRepositoryEntry.FromText(path, "<Project />"));
        if (addition) files.Add(RawRepositoryEntry.FromText("tools/tests/Probe/Added.cs",
            "public class Added { [Xunit.Fact] public void HarmlessAddition() { Xunit.Assert.True(true); } }"));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(files))).Snapshot;
    }
}

using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed class JudgeSeedTests
{
    [Fact]
    public void GeneratedDriverRecoversValidatedTimeAfterCleanStateRestore()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Prepare();
        fixture.Build("driver-cold", 2);
        var driver = fixture.PathOf("build/judge-seed/seed.targets");
        var bytes = File.ReadAllBytes(driver);
        var stamp = File.GetLastWriteTimeUtc(driver);
        fixture.Snapshot();
        Directory.Delete(fixture.PathOf("build/judge-seed"), recursive: true);

        fixture.Restore();

        Assert.Equal(bytes, File.ReadAllBytes(driver));
        fixture.Build("driver-clean-state-warm", 0);
        Assert.Equal(stamp, File.GetLastWriteTimeUtc(driver));
    }

    [Fact]
    public void AlteredGeneratedDriverBytesCannotReuseEvenWithPreservedTime()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Prepare();
        fixture.Build("driver-before-mutation", 2);
        const string driver = "build/judge-seed/seed.targets";
        fixture.WritePreservingTime(driver, File.ReadAllText(fixture.PathOf(driver)) + "\n<!-- altered driver -->\n");

        fixture.Build("driver-altered-bytes", 2);
        fixture.Build("driver-unchanged-bytes", 0);
        fixture.Prepare();
        fixture.Build("driver-regenerated-bytes", 2);
    }

    [Fact]
    public void CompileRegistrationMaterialUsesOnlyTheSelectedProjectProjection()
    {
        using var fixture = new JudgeSeedFixture();
        string Material(string project) => File.ReadAllText(fixture.PathOf(
            $"build/judge-seed/registrations/tools/{project}/{project}.csproj.json"));
        fixture.Prepare();
        var library = Material("Library");
        var consumer = Material("Consumer");
        fixture.EditProjects(registry =>
        {
            var row = registry["projects"]![0]!;
            row["root_namespace"] = "Changed.Namespace";
            row["namespace_exclude"] = new JsonArray("tools/Library/Code.cs");
            row["role"] = "cross-cutting-test";
            row["ci"] = true;
            row["test_partition"] = "explicit-checks";
            row["execution_inputs"] = new JsonArray();
            row["execution_excludes"] = new JsonArray();
            row["execution_environment"] = new JsonArray("STRATALINT_TEST_ENVIRONMENT");
            row["build_inputs"] = new JsonArray("Directory.Build.props");
            registry["rule_build_inputs"] = new JsonArray("Directory.Build.props");
        });
        fixture.Prepare();
        Assert.Equal(library, Material("Library"));
        Assert.Equal(consumer, Material("Consumer"));
        fixture.EditProjects(registry => registry["projects"]![1]!["assembly"] = "UnrelatedToLibrary");
        fixture.Prepare();
        Assert.Equal(library, Material("Library"));
        Assert.NotEqual(consumer, Material("Consumer"));
        consumer = Material("Consumer");
        fixture.EditProjects(registry => registry["projects"]![0]!["include"] = new JsonArray("tools/Library/Code.cs"));
        fixture.Prepare();
        Assert.NotEqual(library, Material("Library"));
        Assert.NotEqual(consumer, Material("Consumer"));
        consumer = Material("Consumer");
        fixture.EditProjects(registry => registry["projects"]![1]!["references"] = new JsonArray());
        fixture.Prepare();
        Assert.NotEqual(consumer, Material("Consumer"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReportSeedValidationUsesOnlyTransportedBundleMembers(bool complete)
    {
        using var fixture = new JudgeSeedFixture();
        using var producer = new ProducerInputFixture();
        var address = producer.Address();
        producer.Plan(address, address);
        var keys = fixture.CacheKeys();
        var partition = keys["partition"]!.GetValue<string>();
        var key = keys["report"]!["key"]!.GetValue<string>();
        var cache = keys["report"]!["path"]!.GetValue<string>();
        var target = keys["report"]!["target"]!.GetValue<string>();
        var name = partition + "/" + new string('a', 64) + "/raw-lean-report.json";
        File.WriteAllText(producer.SeedReportPath + ".seed.json", System.Text.Json.JsonSerializer.Serialize(new
        {
            schema = "lean-report-seed-v1", partition, runtime_sha256 = address[1],
            report_sha256 = Hash(producer.SeedReportPath), materials_sha256 = Hash(producer.SeedReportPath + ".materials.zip"),
        }));
        string[] suffixes = ["", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json"];
        foreach (var suffix in suffixes)
        {
            var destination = fixture.Write(cache + "/data/" + name + suffix, "");
            File.Copy(producer.SeedReportPath + suffix, destination, true);
        }
        fixture.Write(cache + "/manifest.json", System.Text.Json.JsonSerializer.Serialize(new
        {
            schema = "lean-actions-seed-v1", partition, layer = "report", key,
            files = suffixes.Take(complete ? suffixes.Length : 1).Order(StringComparer.Ordinal).Select(suffix => new
            {
                path = name + suffix, sha256 = Hash(fixture.PathOf(cache + "/data/" + name + suffix)),
                mode = OperatingSystem.IsWindows() ? 438 : (int)File.GetUnixFileMode(fixture.PathOf(cache + "/data/" + name + suffix)) & 511,
            }),
        }));
        var restored = fixture.RestoreLayer("report", key);
        Assert.True(restored.Text.Contains(complete ? "\"status\": \"restored\"" : "\"status\": \"miss\"", StringComparison.Ordinal), restored.Text);
        Assert.Equal(complete, File.Exists(fixture.PathOf(target + "/" + name)));

        static string Hash(string path) => Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(path)));
    }

    [Theory]
    [InlineData("dependency")]
    [InlineData("project")]
    public void SeedTransportUsesOnlyItsMaterialManifest(string layer)
    {
        using var fixture = new JudgeSeedFixture();
        var keys = fixture.CacheKeys();
        var cache = keys[layer]!["path"]!.GetValue<string>();
        var target = keys[layer]!["target"]!.GetValue<string>();
        var key = keys[layer]!["key"]!.GetValue<string>();
        var registered = fixture.Write(cache + "/data/registered.txt", "registered material");
        fixture.Write(cache + "/data/unlisted.txt", "unlisted neighbor");
        fixture.Write(cache + "/manifest.json", System.Text.Json.JsonSerializer.Serialize(new
        {
            schema = "lean-actions-seed-v1", partition = keys["partition"]!.GetValue<string>(), layer, key,
            files = new[] { new { path = "registered.txt", mode = OperatingSystem.IsWindows() ? 438 : (int)File.GetUnixFileMode(registered) & 511,
                sha256 = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(registered))) } },
        }));
        var restored = fixture.RestoreLayer(layer, key);
        Assert.Contains("\"status\": \"restored\"", restored.Text, StringComparison.Ordinal);
        Assert.Equal("registered material", File.ReadAllText(fixture.PathOf(target + "/registered.txt")));
        Assert.False(File.Exists(fixture.PathOf(target + "/unlisted.txt")));
        File.WriteAllText(registered, "corrupt bytes");
        var missed = fixture.RestoreLayer(layer, key);
        Assert.Contains("\"status\": \"miss\"", missed.Text, StringComparison.Ordinal);
        Assert.Equal("registered material", File.ReadAllText(fixture.PathOf(target + "/registered.txt")));
    }

    [Theory]
    [InlineData("restore", false)]
    [InlineData("restore", true)]
    [InlineData("snapshot", false)]
    [InlineData("snapshot", true)]
    public void TransportRegistrationErrorsBlockBeforeOptionalCacheHandling(string command, bool duplicate)
    {
        using var fixture = new JudgeSeedFixture();
        if (duplicate) fixture.EditProjects(registry => registry["projects"]!.AsArray().Add(registry["projects"]![0]!.DeepClone()));
        else File.Delete(fixture.PathOf("Meta/engineering-projects.json"));
        var marker = fixture.Write(".judge-binaries/preserved", "existing seed");
        var result = fixture.TransportCommand(command);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("ENGINEERING_PROJECT_REGISTRATION", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("LEAN_ACTIONS_CACHE", result.Text, StringComparison.Ordinal);
        Assert.Equal("existing seed", File.ReadAllText(marker));
    }

    [Fact]
    public void SameBasenameProjectsReuseDistinctReceiptsAndUnlistedTransportIsIgnored()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.UseSameProjectBasenames();
        fixture.Prepare();
        fixture.Build("same-basename-cold", 2);
        foreach (var name in new[] { "Library", "Consumer" })
            Assert.True(File.Exists(fixture.PathOf($"build/judge-seed/receipts/tools/{name}/Project.csproj.seed.json")));
        fixture.Snapshot();
        Assert.True(File.Exists(fixture.SnapshotManifest));
        fixture.AddUnlistedTransportNeighbor();
        fixture.RestoreTransport();
        Assert.False(Directory.Exists(fixture.PathOf(".judge-binaries/data/tools/Neighbor")));
        fixture.Write(".judge-binaries/data/tools/Library/obj/unlisted.dll", "unlisted project material");
        fixture.Write(".judge-binaries/data/build/judge-seed/task/obj/unlisted.dll", "unlisted task material");
        fixture.Prepare();
        Assert.False(File.Exists(fixture.PathOf("tools/Library/obj/unlisted.dll")));
        Assert.False(File.Exists(fixture.PathOf("build/judge-seed/task/obj/unlisted.dll")));
        fixture.Restore();
        fixture.Build("same-basename-warm", 0);
        fixture.Write("tools/Library/Code.cs", "not valid C#");
        Assert.NotEqual(0, fixture.BuildFailure("warm-seed-bad-source").ExitCode);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("duplicate")]
    [InlineData("reference")]
    [InlineData("material")]
    [InlineData("unregistered-project")]
    public void InvalidProjectRegistrationFailsBeforeCacheHandling(string defect)
    {
        using var fixture = new JudgeSeedFixture();
        if (defect == "missing") File.Delete(fixture.PathOf("Meta/engineering-projects.json"));
        else if (defect == "unregistered-project")
        {
            fixture.Write("tools/Neighbor/Neighbor.csproj", "<Project />");
            fixture.Git("add", "tools/Neighbor/Neighbor.csproj");
        }
        else fixture.EditProjects(registry =>
        {
            var rows = registry["projects"]!.AsArray();
            if (defect == "duplicate") rows.Add(rows[0]!.DeepClone());
            if (defect == "reference") rows[0]!["references"]!.AsArray().Add("tools/Missing/Missing.csproj");
            if (defect == "material") rows[0]!["include"]!.AsArray().Add("tools/Library/Missing.cs");
        });
        var paths = new[] { "tools/Library/bin/existing", "tools/Library/obj/existing", ".judge-binaries/existing" }
            .Select(path => fixture.Write(path, "preserved")).ToArray();

        var result = fixture.Prepare(success: false);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("ENGINEERING_PROJECT_REGISTRATION", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("\"status\": \"miss\"", result.Text, StringComparison.Ordinal);
        foreach (var path in paths) Assert.Equal("preserved", File.ReadAllText(path));
    }

    [Fact]
    public void UnrelatedRegisteredProofDoesNotInvalidateCompilerSeedsOrGetBuilt()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Write("tools/Proof/Proof.csproj", "<Project />");
        fixture.Write("tools/Proof/Bad.cs", "deliberately invalid C#");
        fixture.EditProjects(registry => registry["projects"]!.AsArray().Add(System.Text.Json.JsonSerializer.SerializeToNode(
            JudgeSeedFixture.ProjectRow("tools/Proof/Proof.csproj", "Proof", "compile-fail-proof", ["tools/Proof/Bad.cs"], []))));
        fixture.Git("add", "tools/Proof");
        var neighbor = fixture.Write("tools/Neighbor/obj/preserved", "unregistered output");
        fixture.Prepare();
        fixture.Build("registered-cold", 2);
        fixture.EditProjects(registry => registry["projects"]![2]!["assembly"] = "ChangedProof");
        fixture.Prepare();
        fixture.Build("unrelated-registry-row", 0);
        Assert.Equal("unregistered output", File.ReadAllText(neighbor));
        Assert.False(Directory.Exists(fixture.PathOf("tools/Proof/bin")));
        fixture.EditProjects(registry =>
        {
            registry["projects"]![0]!["role"] = "production";
            registry["projects"]![0]!["owned_test_assembly"] = "Library.Tests";
        });
        fixture.Prepare();
        fixture.Build("relevant-registry-closure", 2);
        fixture.Snapshot();
        Assert.True(File.Exists(fixture.SnapshotManifest));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("version")]
    [InlineData("material")]
    public void InvalidSeedRegistrationFailsBeforeInstallingMaterial(string defect)
    {
        using var fixture = new JudgeSeedFixture();
        var path = fixture.PathOf("Meta/judge-seed.json");
        if (defect == "missing") File.Delete(path);
        else
        {
            var registry = JsonNode.Parse(File.ReadAllText(path))!;
            if (defect == "version") registry["sdk_version"] = "0.0.0";
            else registry["sdk_files"]!.AsArray().Add("missing-required.dll");
            File.WriteAllText(path, registry.ToJsonString());
        }
        var preserved = fixture.Write("tools/Library/bin/existing", "retain until registration is valid");

        var result = fixture.Prepare(success: false);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("JUDGE_SEED_REGISTRATION", result.Text, StringComparison.Ordinal);
        Assert.Equal("retain until registration is valid", File.ReadAllText(preserved));
    }

    [Theory]
    [InlineData("version", "1")]
    [InlineData("version", "0")]
    [InlineData("sdk_version", "\"0.0.0\"")]
    [InlineData("target_framework", "\"net9.0\"")]
    [InlineData("sdk_files", "[]")]
    [InlineData("repository_files", "[]")]
    public void DuplicateSeedRegistrationFieldsFailBeforeInstallingMaterial(string field, string earlierValue)
    {
        using var fixture = new JudgeSeedFixture();
        var path = fixture.PathOf("Meta/judge-seed.json");
        var original = File.ReadAllText(path);
        fixture.Write("Meta/judge-seed.json", $"{{\"{field}\":{earlierValue}," + original[1..]);

        AssertRegistrationRejected(fixture, "duplicate JSON field: " + field);
    }

    [Theory]
    [InlineData("sdk", "{\"sdk\":{\"version\":\"0.0.0\"},\"sdk\":{\"version\":\"10.0.103\"}}")]
    [InlineData("version", "{\"sdk\":{\"version\":\"0.0.0\",\"version\":\"10.0.103\"}}")]
    public void DuplicateGlobalSdkFieldsFailBeforeInstallingMaterial(string field, string json)
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Write("global.json", json);

        AssertRegistrationRejected(fixture, "duplicate JSON field: " + field);
    }

    [Theory]
    [InlineData("true")]
    [InlineData("1.0")]
    public void NonIntegerSeedVersionFailsBeforeInstallingMaterial(string version)
    {
        using var fixture = new JudgeSeedFixture();
        var path = fixture.PathOf("Meta/judge-seed.json");
        var registry = JsonNode.Parse(File.ReadAllText(path))!;
        registry["version"] = JsonNode.Parse(version);
        File.WriteAllText(path, registry.ToJsonString());

        AssertRegistrationRejected(fixture, "invalid judge seed manifest schema");
    }

    [Theory]
    [InlineData("sdk_files", "Roslyn/bincore/csc.dll")]
    [InlineData("sdk_files", "Roslyn/bincore/*.dll")]
    [InlineData("repository_files", "Directory.Build.props")]
    [InlineData("repository_files", "*.props")]
    public void DuplicateDeclaredMaterialPatternsFailBeforeInstallingMaterial(string field, string pattern)
    {
        using var fixture = new JudgeSeedFixture();
        var path = fixture.PathOf("Meta/judge-seed.json");
        var registry = JsonNode.Parse(File.ReadAllText(path))!;
        registry[field] = new JsonArray(pattern, pattern);
        File.WriteAllText(path, registry.ToJsonString());

        AssertRegistrationRejected(fixture, "duplicate registered material pattern: " + pattern);
    }

    private static void AssertRegistrationRejected(JudgeSeedFixture fixture, string diagnostic)
    {
        var preserved = new[] { "tools/Library/bin/existing", "tools/Library/obj/existing", ".judge-binaries/existing" }
            .Select(path => fixture.Write(path, "retain until registration is valid")).ToArray();

        var result = fixture.Prepare(success: false);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("JUDGE_SEED_REGISTRATION", result.Text, StringComparison.Ordinal);
        Assert.Contains(diagnostic, result.Text, StringComparison.Ordinal);
        foreach (var path in preserved) Assert.Equal("retain until registration is valid", File.ReadAllText(path));
    }

    [Fact]
    public void DeclaredCompilerBytesChangeIdentityAndUndeclaredSdkFilesDoNot()
    {
        using var fixture = new JudgeSeedFixture();
        var path = fixture.PathOf("Meta/judge-seed.json");
        var registry = JsonNode.Parse(File.ReadAllText(path))!;
        registry["sdk_files"] = new JsonArray("declared/*.dll");
        File.WriteAllText(path, registry.ToJsonString());
        fixture.Write("extra-sdk/sdk/10.0.103/declared/compiler.dll", "first registered bytes");
        fixture.Write("extra-sdk/sdk/10.0.103/unregistered.dll", "undeclared bytes");
        var first = fixture.ReadFakeSdkMaterial().Text;
        fixture.Write("extra-sdk/sdk/10.0.103/unregistered.dll", "different undeclared bytes");
        Assert.Equal(first, fixture.ReadFakeSdkMaterial().Text);
        fixture.Write("extra-sdk/sdk/10.0.103/declared/compiler.dll", "changed registered bytes");
        Assert.NotEqual(first, fixture.ReadFakeSdkMaterial().Text);
        fixture.Write("extra-sdk/sdk/10.0.103/declared/new.dll", "registered glob addition");
        Assert.Contains("new.dll", fixture.ReadFakeSdkMaterial().Text, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckoutSeedReuseAndRuntimeCopyFollowTheRealCompiler()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Prepare();
        fixture.Build("cold", 2);
        var original = File.ReadAllBytes(fixture.Dll("Consumer"));
        foreach (var environment in new[] { new[] { "GITHUB_EVENT_NAME=pull_request_target" }, new[] { "GITHUB_EVENT_NAME=pull_request" },
                     new[] { "GITHUB_EVENT_NAME=workflow_dispatch" }, new[] { "GITHUB_REF=refs/heads/other" }, new[] { "STRATALINT_CACHE_WRITES=false" },
                     new[] { "STRATALINT_BUILD_SUCCEEDED=false", "STRATALINT_CHECK_SUCCEEDED=true" }, new[] { "STRATALINT_BUILD_SUCCEEDED=" } })
        {
            fixture.Snapshot(environment);
            Assert.False(File.Exists(fixture.SnapshotManifest));
        }
        fixture.Snapshot();
        Assert.True(File.Exists(fixture.SnapshotManifest));
        fixture.Restore();
        fixture.Build("new-checkout", 0);
        Assert.Equal(original, File.ReadAllBytes(fixture.Dll("Consumer")));
        fixture.Write("tools/Library/Code.cs", "public static class Library { public static int Value() => 2; }");
        fixture.Build("dependency-implementation", 1);
        Assert.Equal(original, File.ReadAllBytes(fixture.Dll("Consumer")));
        Assert.Equal(File.ReadAllBytes(fixture.Dll("Library")), File.ReadAllBytes(fixture.Dll("Consumer", "Library")));
        Assert.Equal("2", fixture.Dotnet([fixture.Dll("Consumer")]).Text.Trim());
        fixture.WritePreservingTime("tools/Consumer/data.sh", "echo changed\n");
        fixture.Build("copied-data", 0);
        Assert.Equal("echo changed\n", File.ReadAllText(Path.Combine(Path.GetDirectoryName(fixture.Dll("Consumer"))!, "data.sh")));
        fixture.Write("tools/Library/Code.cs", "public static class Library { public static int Value() => 2; public static int Added() => 0; }");
        fixture.Build("registered-reference-api-change", 2);
        Assert.Equal("2", fixture.Dotnet([fixture.Dll("Consumer")]).Text.Trim());
    }

    [Fact]
    public void OptionsRegisteredMembershipAndResourcesMatchACleanBuild()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Prepare();
        fixture.Build("cold", 2);
        fixture.Build("option", 2, "-p:Optimize=false");
        var incremental = fixture.Products();
        fixture.Build("clean-option", 2, "-p:Optimize=false", "-t:Rebuild");
        Assert.Equal(incremental, fixture.Products());
        fixture.Write("tools/Library/Added.cs", "// registered Compile glob member\n");
        fixture.Git("add", "tools/Library/Added.cs");
        fixture.Prepare();
        fixture.Build("membership", 1, "-p:Optimize=false");
        var project = fixture.PathOf("tools/Library/Library.csproj");
        File.WriteAllText(project, File.ReadAllText(project).Replace("</Project>",
            "<PropertyGroup><DefineConstants>CHANGED</DefineConstants></PropertyGroup></Project>", StringComparison.Ordinal));
        fixture.Build("project", 1, "-p:Optimize=false");
        File.Delete(fixture.PathOf("tools/Library/Added.cs"));
        fixture.Git("add", "tools/Library/Added.cs");
        fixture.Prepare();
        fixture.Build("removed-input", 1, "-p:Optimize=false");
        fixture.WritePreservingTime("tools/Library/message.txt", "changed resource");
        fixture.Build("preserved-time-resource", 1, "-p:Optimize=false");
        fixture.Write("tools/Library/generator-input.txt", "changed additional input");
        fixture.Build("additional-input", 1, "-p:Optimize=false");
        fixture.Build("generated-assembly-info", 2, "-p:Optimize=false", "-p:Version=2.0.0");
    }

    [Fact]
    public void CorruptMissingTransportAndRelocatedMaterialFallBackToTheCompiler()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Prepare();
        fixture.Build("cold", 2);
        fixture.Snapshot();
        fixture.CorruptSnapshot();
        fixture.Restore();
        fixture.Build("corrupt-transfer", 2);
        fixture.Snapshot();
        var nullInventory = JsonNode.Parse(File.ReadAllText(fixture.SnapshotManifest))!;
        nullInventory["files"] = null;
        File.WriteAllText(fixture.SnapshotManifest, nullInventory.ToJsonString());
        fixture.Restore();
        fixture.Build("null-inventory-transfer", 2);
        fixture.Snapshot();
        fixture.Restore();
        fixture.Build("runtime-rematerialization", 0);
        var original = File.ReadAllBytes(fixture.Dll("Consumer"));
        File.Delete(fixture.Dll("Consumer"));
        fixture.Build("missing-runtime", 0);
        fixture.WritePreservingTime("tools/Consumer/bin/Release/net10.0/Consumer.dll", "corrupt");
        fixture.Build("preserved-time-runtime-corruption", 0);
        Assert.Equal(original, File.ReadAllBytes(fixture.Dll("Consumer")));
        fixture.WritePreservingTime("tools/Consumer/obj/Release/net10.0/Consumer.dll", "corrupt");
        fixture.Build("preserved-time-intermediate-corruption", 1);
        Assert.Equal(original, File.ReadAllBytes(fixture.Dll("Consumer")));
        File.Delete(fixture.PathOf("tools/Consumer/obj/Release/net10.0/Consumer.pdb"));
        fixture.Build("missing-intermediate", 1);
        fixture.Snapshot();
        fixture.RestoreWithMissingTransferredProject();
        fixture.Build("partial-transfer", 2);
        fixture.Snapshot();
        fixture.Relocate();
        fixture.Restore();
        fixture.Build("unsupported-relocation", 2);
        Assert.Equal("1", fixture.Dotnet([fixture.Dll("Consumer")]).Text.Trim());
    }

    [Fact]
    public void NoSeedAndSaveFailureCannotPassBadCompilation()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.Prepare();
        fixture.Write("tools/Library/Code.cs", "not valid C#");
        Assert.NotEqual(0, fixture.BuildFailure("no-seed-bad-source").ExitCode);
        fixture.Write("tools/Library/Code.cs", "public static class Library { public static int Value() => 1; }");
        fixture.Build("repair", 2);
        fixture.FailSnapshotSave();
        Assert.False(File.Exists(fixture.SnapshotManifest));
        fixture.Write("tools/Library/Code.cs", "not valid C#");
        Assert.NotEqual(0, fixture.BuildFailure("save-failed-bad-source").ExitCode);
    }

    [Fact]
    public void HelperReadmeCommitReusesButSourceChangeCompiles()
    {
        using var fixture = new JudgeSeedFixture();
        fixture.InitializeGit();
        var before = fixture.Git("rev-parse", "HEAD", "HEAD^{tree}").Text;
        fixture.BuildHelper("helper-cold", 1);
        var dll = fixture.Dll("scripts/report", "JudgeSeedTask");
        var original = File.ReadAllBytes(dll);
        fixture.Write("README.md", "changed documentation\n");
        fixture.Git("add", "README.md");
        fixture.Git("commit", "--quiet", "-m", "README only");
        Assert.NotEqual(before, fixture.Git("rev-parse", "HEAD", "HEAD^{tree}").Text);
        Assert.Equal("README.md", fixture.Git("diff", "--name-only", "HEAD^1", "HEAD").Text.Trim());
        fixture.BuildHelper("helper-readme", 0);
        Assert.Equal(original, File.ReadAllBytes(dll));
        File.AppendAllText(fixture.PathOf("tools/scripts/report/JudgeSeedTask.cs"), "\ninternal static class ChangedHelperSource { }\n");
        fixture.BuildHelper("helper-source", 1);
        Assert.NotEqual(original, File.ReadAllBytes(dll));
    }
}

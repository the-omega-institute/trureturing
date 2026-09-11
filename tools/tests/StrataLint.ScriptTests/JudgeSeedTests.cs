using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed class JudgeSeedTests
{
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
        fixture.Build("membership", 1, "-p:Optimize=false");
        var project = fixture.PathOf("tools/Library/Library.csproj");
        File.WriteAllText(project, File.ReadAllText(project).Replace("</Project>",
            "<PropertyGroup><DefineConstants>CHANGED</DefineConstants></PropertyGroup></Project>", StringComparison.Ordinal));
        fixture.Build("project", 1, "-p:Optimize=false");
        File.Delete(fixture.PathOf("tools/Library/Added.cs"));
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

using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed partial class ScriptTestGateClosureTests
{
    private const string EngineeringScopeProject =
        "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj";
    private const string EngineProject =
        "tools/StrataLint.Engine/StrataLint.Engine.csproj";
    private const string TestSupportProject =
        "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj";
    private const string TruthProject =
        "tools/Trureturing.Truth/Trureturing.Truth.csproj";
    private const string EmptyPackageLock =
        "{\"version\":2,\"dependencies\":{\"net10.0\":{}}}\n";
    private const string XunitPackageLock =
        "{\"version\":2,\"dependencies\":{\"net10.0\":{"
        + "\"xunit.assert\":{\"type\":\"Transitive\",\"resolved\":\"2.9.3\"},"
        + "\"xunit.extensibility.core\":{\"type\":\"Transitive\",\"resolved\":\"2.9.3\"}}}}\n";
    private const string DirectoryBuildProps =
        "<Project><PropertyGroup><TargetFramework>net10.0</TargetFramework>"
        + "<ImplicitUsings>enable</ImplicitUsings></PropertyGroup></Project>\n";

    private static RepositorySnapshot CurrentSnapshot() => Decode(RawRepositorySnapshot.Create(
    [
        RawRepositoryEntry.FromText(ScriptTestsProject, ScriptTestsProjectText()),
        RawRepositoryEntry.FromText(ScriptTestsSource, ScriptTestsSourceText()),
        RawRepositoryEntry.FromText(
            "tools/tests/StrataLint.ScriptTests/packages.lock.json",
            XunitPackageLock),
        RawRepositoryEntry.FromText(
            EngineeringScopeProject,
            ProjectText(EngineeringScopeProject, EngineProject)),
        RawRepositoryEntry.FromText(
            "tools/StrataLint.EngineeringScope/Program.cs",
            "namespace StrataLint.EngineeringScope; internal static class Program { }\n"),
        RawRepositoryEntry.FromText(
            "tools/StrataLint.EngineeringScope/packages.lock.json",
            EmptyPackageLock),
        RawRepositoryEntry.FromText(EngineProject, ProjectText(EngineProject, TruthProject)),
        RawRepositoryEntry.FromText(
            "tools/StrataLint.Engine/GitRepositorySnapshotReader.cs",
            "namespace StrataLint.Engine; public static class GitRepositorySnapshotReader "
            + "{ public static object ReadCurrent(string root) => new(); }\n"),
        RawRepositoryEntry.FromText("tools/StrataLint.Engine/packages.lock.json", EmptyPackageLock),
        RawRepositoryEntry.FromText(TestSupportProject, TestSupportProjectText()),
        RawRepositoryEntry.FromText(
            "tools/tests/StrataLint.Tests/TestProcessRunner.cs",
            TestSupportSourceText()),
        RawRepositoryEntry.FromText(
            "tools/tests/StrataLint.Tests/packages.lock.json",
            XunitPackageLock),
        RawRepositoryEntry.FromText(TruthProject, ProjectText(TruthProject)),
        RawRepositoryEntry.FromText(
            "tools/Trureturing.Truth/Truth.cs",
            "namespace Trureturing.Truth; public sealed class Truth { }\n"),
        RawRepositoryEntry.FromText("tools/Trureturing.Truth/packages.lock.json", EmptyPackageLock),
        RawRepositoryEntry.FromText("Directory.Build.props", DirectoryBuildProps),
        RawRepositoryEntry.FromText("Directory.Packages.props", "<Project />\n"),
        RawRepositoryEntry.FromText(
            "global.json",
            "{\"sdk\":{\"version\":\"10.0.103\",\"rollForward\":\"latestMinor\"}}\n"),
        RawRepositoryEntry.FromText(PlaybookScript, "#!/usr/bin/env bash\nexit 0\n"),
        RawRepositoryEntry.FromText(
            "tools/scripts/workflow/self-lock-probe.sh",
            "#!/usr/bin/env bash\nexit 0\n"),
        RawRepositoryEntry.FromText(
            "tools/scripts/report/report-supervisor.sh",
            "#!/usr/bin/env bash\nexit 0\n"),
        RawRepositoryEntry.FromText(".github/workflows/ci.yml", "name: synthetic\n"),
    ]));

    private static string ProjectText(string owner, params string[] references) =>
        "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup>"
        + string.Concat(references.Select(reference =>
            $"<ProjectReference Include=\"{RelativeProjectPath(owner, reference)}\" />"))
        + "</ItemGroup></Project>\n";

    private static string ScriptTestsProjectText() =>
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>"
        + "<IsTestProject>true</IsTestProject><AssemblyName>StrataLint.ScriptTests</AssemblyName>"
        + "</PropertyGroup><ItemGroup>"
        + $"<ProjectReference Include=\"{RelativeProjectPath(ScriptTestsProject, EngineeringScopeProject)}\" />"
        + $"<ProjectReference Include=\"{RelativeProjectPath(ScriptTestsProject, EngineProject)}\" />"
        + $"<ProjectReference Include=\"{RelativeProjectPath(ScriptTestsProject, TestSupportProject)}\" />"
        + "<PackageReference Include=\"xunit\" Version=\"2.9.3\" />"
        + "</ItemGroup></Project>\n";

    private static string TestSupportProjectText() =>
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>"
        + "<IsTestProject>true</IsTestProject><AssemblyName>StrataLint.Tests</AssemblyName>"
        + "</PropertyGroup><ItemGroup>"
        + "<PackageReference Include=\"xunit\" Version=\"2.9.3\" />"
        + "</ItemGroup></Project>\n";

    private static string RelativeProjectPath(string owner, string reference) => Path.GetRelativePath(
        Path.GetDirectoryName(owner)!,
        reference).Replace('\\', '/');

    private static string ScriptTestsSourceText() =>
        "using StrataLint.Engine; using Xunit; namespace StrataLint.Tests; "
        + "public sealed class PlaybookWorkflowScriptTests "
        + "{ [Fact] public void SyntheticBaseline() { "
        + "ScriptHarnessScratch.CopyScriptInto(Path.Combine("
        + RepositoryRootCall
        + ", \"tools/scripts/workflow/playbook-workflows.sh\"), "
        + "Path.Combine(TestScratchRoot.Current.Path, \"probe.sh\")); } }\n";

    private static string TestSupportSourceText() =>
        "namespace StrataLint.Tests; "
        + "public sealed class TemporaryDirectory : IDisposable "
        + "{ public string Path => string.Empty; public void Dispose() { } } "
        + "public static class ScriptHarnessScratch "
        + "{ public static void CopyScriptInto(string source, string target) { } } "
        + "public static class TestRepositoryLayout { public static string FindRoot() => string.Empty; "
        + "public static string ReadAllText(string path) => string.Empty; } "
        + "public sealed class TestScratchRoot "
        + "{ public static TestScratchRoot Current { get; } = new(); public string Path => string.Empty; } "
        + "public static class TestBudgets "
        + "{ public static TimeSpan ScriptProcessHangGuard => TimeSpan.Zero; } "
        + "public static class TestProcessRunner "
        + "{ public static object Run(string file, IReadOnlyList<string> arguments, "
        + "string workingDirectory, TimeSpan timeout, int maxOutputBytes) => new(); }\n";
}

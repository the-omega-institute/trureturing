using System.Text.Json.Nodes;
using StrataLint.EngineeringScope;

namespace StrataLint.TestSupport;

internal static class PreflightFixture
{
    internal static void Configure(ResourceFixture fixture)
    {
        foreach (var path in new[] { "tools/scripts/preflight.sh", "tools/scripts/ci-stage.sh",
                     "tools/scripts/lib/resource-observation-lib.sh" })
            fixture.Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
        // Explicit external adapters: empty seed preparation, supervisor pass-through,
        // and the bootstrap runner location. None supplies a build acceptance receipt.
        fixture.Write("tools/scripts/report/dotnet_producer.py", "import pathlib,sys\np=pathlib.Path(sys.argv[2])/'build/judge-seed/seed.targets'\np.parent.mkdir(parents=True,exist_ok=True)\np.write_text('<Project />')\n");
        fixture.Write("tools/scripts/report/report-supervisor.sh", "while [[ $1 != -- ]]; do shift; done\nshift\nexec \"$@\"\n");
        fixture.Write("NuGet.Config", "<configuration><packageSources><clear /></packageSources></configuration>\n");
        fixture.Write(ResourceFixture.Foo, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <AssemblyName>StrataLint</AssemblyName><OutputType>Exe</OutputType>
            <BaseOutputPath>../StrataLint.Cli/bin/</BaseOutputPath>
            <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>
            """);
        fixture.Write("tools/Foo/packages.lock.json", "{\"version\":1,\"dependencies\":{\"net10.0\":{}}}\n");
        fixture.Write("tools/Foo/Program.cs", """
            if (args.Length != 3 || args[0] != "filemap-conform" || args[1] != "--scope" || !System.IO.File.Exists(args[2])) return 91;
            System.IO.File.AppendAllText("build/launched", "dotnet filemap-conform\n");
            System.Console.WriteLine("fixture filemap check reached");
            return 0;
            """);
        var registry = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
        registry["projects"]!.AsArray().Single(p => p!["path"]!.ToString() == ResourceFixture.Foo)!["assembly"] = "StrataLint";
        fixture.Write(EngineeringRegistrationFixture.Path, registry.ToJsonString());
    }

    internal static Dictionary<string, string> EnvironmentFor(ResourceFixture fixture)
    {
        var bin = Path.Combine(fixture.Root, "build/cold-bin");
        Directory.CreateDirectory(bin);
        var realDotnet = EngineeringProcess.Process(fixture.Root, "/bin/bash", ["-c", "command -v dotnet"]).Text.Trim();
        File.WriteAllText(Path.Combine(bin, "dotnet"), """
            #!/bin/bash
            set -euo pipefail
            runner=tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll
            if [[ "$1" == "$runner" ]]; then shift; exec "$CONTRACT_NATIVE" "$@"; fi
            if [[ "${2:-}" == tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj ]]; then
              printf 'bootstrap-%s\n' "$1" >> "$CONTRACT_EVENTS"
              if [[ "$1" == build ]]; then mkdir -p "$(dirname "$runner")"; printf 'native runner location adapter\n' > "$runner"; fi
              exit 0
            fi
            printf '%s\n' "$*" >> "$CONTRACT_EVENTS"
            exec "$CONTRACT_DOTNET" "$@"
            """);
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(bin, "dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var environment = new Dictionary<string, string> { ["PATH"] = bin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            ["CONTRACT_NATIVE"] = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope"),
            ["CONTRACT_DOTNET"] = realDotnet, ["CONTRACT_EVENTS"] = Path.Combine(fixture.Root, "build/cold-events"),
            ["CI_PLAN_PATH"] = "", ["CI_CHANGES_PATH"] = "",
            ["CI_BUILD_ROUND"] = "", ["CANDIDATE_SHA"] = "", ["GITHUB_EVENT_NAME"] = "", ["CI_NEEDS"] = "{}", ["CI_WORKFLOW_INPUTS"] = "null" };
        foreach (var pair in fixture.DotnetProfile()) environment[pair.Key] = pair.Value;
        return environment;
    }

}

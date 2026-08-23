using System.Globalization;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void WorktreeHoldAndReleaseReuseTheWorktreeDestinationExpression()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var destinationDefinitions = Regex.Matches(
            makefile,
            @"(?m)^WORKTREE_DEST\s*=",
            RegexOptions.CultureInvariant);

        Assert.Single(destinationDefinitions.Cast<Match>());
        Assert.Contains(
            "WORKTREE_DEST = $(if $(DEST),$(abspath $(DEST)),$(abspath ../trureturing-$(NAME)))",
            makefile,
            StringComparison.Ordinal);

        var createRecipe = Recipe(makefile, "worktree");
        var holdRecipe = Recipe(makefile, "worktree-hold");
        var releaseRecipe = Recipe(makefile, "worktree-release");
        Assert.All(
            new[] { createRecipe, holdRecipe, releaseRecipe },
            recipe => Assert.Contains("\"$(WORKTREE_DEST)\"", recipe, StringComparison.Ordinal));
        Assert.DoesNotContain("../trureturing-", holdRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("../trureturing-", releaseRecipe, StringComparison.Ordinal);
        Assert.Contains("-- worktree hold", holdRecipe, StringComparison.Ordinal);
        Assert.Contains("--reason \"$(REASON)\"", holdRecipe, StringComparison.Ordinal);
        Assert.Contains("-- worktree release", releaseRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("git worktree", holdRecipe + releaseRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("worktree-destination-guard", makefile, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("worktree-hold", "hold", "seat reason with spaces")]
    [InlineData("worktree-release", "release", "")]
    public void WorktreeHoldAndReleaseTargetsExecuteTheCliContract(
        string target,
        string operation,
        string reason)
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var cliDirectory = Path.Combine(fixture.Path, "tools", "StrataLint.Cli");
        var destination = Path.Combine(fixture.Path, "controlled-lane");
        var dotnetPath = Path.Combine(binDirectory, "dotnet");
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(cliDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        File.WriteAllText(
            dotnetPath,
            """
            #!/usr/bin/env bash
            printf '%s\0' "$@" > "$DOTNET_ARGV"
            receipt="{\"event\":\"worktree_hold_state\",\"operation\":\"$EXPECTED_OPERATION\"}"
            if [[ "$DOTNET_EXIT_CODE" == 0 ]]; then
              printf '%s\n' "$receipt"
            else
              printf '%s\n' "$receipt" >&2
            fi
            exit "$DOTNET_EXIT_CODE"
            """ + "\n",
            new UTF8Encoding(false));
        File.SetUnixFileMode(
            dotnetPath,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var successArguments = Path.Combine(fixture.Path, "success.argv");
        var success = RunTarget(
            fixture.Path,
            binDirectory,
            successArguments,
            0,
            target,
            operation,
            destination,
            reason);

        Assert.True(
            success.ExitCode == 0,
            $"expected exit 0, got {success.ExitCode}; stderr: "
                + Encoding.UTF8.GetString(success.StandardError));
        Assert.Empty(success.StandardError);
        AssertCliReceipt(success.StandardOutput, operation);
        AssertCliArguments(operation, destination, reason, ReadArguments(successArguments));

        var failureArguments = Path.Combine(fixture.Path, "failure.argv");
        var failure = RunTarget(
            fixture.Path,
            binDirectory,
            failureArguments,
            23,
            target,
            operation,
            destination,
            reason);

        Assert.Equal(2, failure.ExitCode);
        Assert.Empty(failure.StandardOutput);
        var failureError = Encoding.UTF8.GetString(failure.StandardError);
        Assert.StartsWith(
            $"{{\"event\":\"worktree_hold_state\",\"operation\":\"{operation}\"}}\n",
            failureError,
            StringComparison.Ordinal);
        Assert.Contains("Error 23", failureError, StringComparison.Ordinal);
        AssertCliArguments(operation, destination, reason, ReadArguments(failureArguments));
    }

    public static IEnumerable<object[]> EffectiveWorktreeWhitespaceCases()
    {
        string[] targets = ["worktree", "worktree-hold", "worktree-release"];
        object[][] inputs =
        [
            ["trailing-destination", "trailing ", "controlled", true, 2],
            ["leading-and-trailing-destination", " leading ", "controlled", true, 2],
            ["embedded-space-destination", "embed ded", "controlled", true, 2],
            ["embedded-tab-destination", "embed\tded", "controlled", true, 2],
            ["trailing-name-fallback", null!, "trailing-name ", false, 2],
            ["embedded-tab-name-fallback", null!, "embedded\tname", false, 2],
            ["clean-destination", "controlled", "fallback", true, 0],
            ["leading-destination", " leading", "fallback", true, 0],
            ["whitespace-only-destination", " ", "controlled", true, 0],
            ["tab-only-destination", "\t", "controlled", true, 0],
            ["leading-name-fallback", null!, " leading-name", false, 0],
            ["whitespace-only-name-fallback", null!, " ", false, 0],
        ];

        foreach (var target in targets)
        {
            foreach (var input in inputs)
            {
                yield return [target, .. input];
            }
        }
    }

    [Theory]
    [MemberData(nameof(EffectiveWorktreeWhitespaceCases))]
    public void WorktreeTargetsValidateOnlyWhitespaceVisibleInTheEffectiveMakeValue(
        string target,
        string shape,
        string? destination,
        string name,
        bool includeDestination,
        int expectedExitCode)
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var scriptsDirectory = Path.Combine(fixture.Path, "tools", "scripts");
        var marker = Path.Combine(fixture.Path, "mutation.marker");
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(scriptsDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            "#!/usr/bin/env bash\ntouch \"$MUTATION_MARKER\"\n");
        WriteExecutable(
            Path.Combine(scriptsDirectory, "worktree-init.sh"),
            "#!/usr/bin/env bash\ntouch \"$MUTATION_MARKER\"\n");

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "export PATH=\"$1:$PATH\" MUTATION_MARKER=\"$2\"; "
                    + "args=(\"$3\" \"NAME=$5\"); "
                    + "if [[ \"$6\" == 1 ]]; then args+=(\"DEST=$4\"); fi; "
                    + "exec make --no-print-directory \"${args[@]}\"",
                "worktree-effective-whitespace",
                binDirectory,
                marker,
                target,
                destination ?? string.Empty,
                name,
                includeDestination ? "1" : "0",
            ],
            fixture.Path,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.True(
            result.ExitCode == expectedExitCode,
            $"{shape}: expected exit {expectedExitCode}, got {result.ExitCode}; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
        Assert.Empty(result.StandardOutput);
        if (expectedExitCode == 2)
        {
            Assert.Contains(
                "WORKTREE_DEST_WHITESPACE",
                Encoding.UTF8.GetString(result.StandardError),
                StringComparison.Ordinal);
            Assert.False(File.Exists(marker));
            return;
        }
        Assert.Empty(result.StandardError);
        Assert.True(File.Exists(marker), $"{shape}: target did not reach its mutation command");
    }

    [Fact]
    public void WorktreeHelpDisclosesMakeWhitespaceNormalizationResidual()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = BoundedProcessRunner.Run(
            "make",
            ["--no-print-directory", "help"],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "Worktree destination validation rejects embedded/trailing whitespace; Make removes "
                + "leading/whitespace-only DEST or fallback NAME before recipes can inspect it",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    private static ProcessOutput RunTarget(
        string workingDirectory,
        string binDirectory,
        string argumentReceipt,
        int exitCode,
        string target,
        string operation,
        string destination,
        string reason) =>
        BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" DOTNET_ARGV=\"$2\" DOTNET_EXIT_CODE=\"$3\" "
                    + "EXPECTED_OPERATION=\"$4\" exec make --no-print-directory \"$5\" "
                    + "NAME=controlled DEST=\"$6\" REASON=\"$7\"",
                "worktree-hold-make",
                binDirectory,
                argumentReceipt,
                exitCode.ToString(CultureInfo.InvariantCulture),
                operation,
                target,
                destination,
                reason,
            ],
            workingDirectory,
            TimeSpan.FromSeconds(30),
            64 * 1024);

    private static string[] ExpectedCliArguments(
        string operation,
        string destination,
        string reason)
    {
        var arguments = new List<string>
        {
            "run",
            "--project",
            "tools/StrataLint.Cli/StrataLint.Cli.csproj",
            "--configuration",
            "Release",
            "--",
            "worktree",
            operation,
            "--path",
            destination,
        };
        if (operation == "hold")
        {
            arguments.Add("--reason");
            arguments.Add(reason);
        }

        return arguments.ToArray();
    }

    private static string[] ReadArguments(string path)
    {
        var arguments = Encoding.UTF8.GetString(File.ReadAllBytes(path)).Split('\0');
        Assert.Equal(string.Empty, arguments[^1]);
        return arguments[..^1];
    }

    private static void AssertCliArguments(
        string operation,
        string destination,
        string reason,
        string[] actual)
    {
        var expected = ExpectedCliArguments(operation, destination, reason);
        Assert.True(
            expected.SequenceEqual(actual, StringComparer.Ordinal),
            $"expected argv: {string.Join(" | ", expected)}{Environment.NewLine}"
                + $"actual argv: {string.Join(" | ", actual)}");
    }

    private static void AssertCliReceipt(byte[] bytes, string operation)
    {
        var output = Encoding.UTF8.GetString(bytes);
        Assert.EndsWith("\n", output, StringComparison.Ordinal);
        using var document = JsonDocument.Parse(output);
        Assert.Equal("worktree_hold_state", document.RootElement.GetProperty("event").GetString());
        Assert.Equal(operation, document.RootElement.GetProperty("operation").GetString());
    }

}

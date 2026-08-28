using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection(FrozenGitProcessEnvironmentCollection.Name)]
public sealed class FrozenGitInfrastructureFixtureTests
{
    [Fact]
    public void GitExecutableUnavailableExitIsNotReportedAsMissingLedgerObject()
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        using var launcher = new TemporaryDirectory();
        var git = Path.Combine(launcher.Path, "git");
        File.WriteAllText(
            git,
            """
            #!/bin/sh
            if [ "$1" = "rev-parse" ] && [ "$2" = "--show-object-format" ]; then
              printf 'sha1\n'
              exit 0
            fi
            printf '/missing/git: executable not found\n' >&2
            exit 127
            """,
            new UTF8Encoding(false));
        File.SetUnixFileMode(
            git,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var previousPath = Environment.GetEnvironmentVariable("PATH");
        Environment.SetEnvironmentVariable("PATH", launcher.Path);

        try
        {
            var references = FrozenLedgerReferenceSet.Create(
                ImmutableArray<FrozenLedgerInput>.Empty,
                ImmutableArray<string>.Empty,
                ["git-sha1:" + new string('f', 40)],
                Array.Empty<string>(),
                Array.Empty<string>());

            var exception = Assert.Throws<GitInfrastructureException>(() =>
                new GitRepositoryGateway(repository.Path).ValidateFrozenReferences(references));

            Assert.Equal(GitCommandFailureKind.NonzeroExit, exception.Failure.Kind);
            Assert.Equal(127, exception.Failure.ExitCode);
            Assert.DoesNotContain("not a reachable", exception.Message, StringComparison.Ordinal);
            Assert.Contains("exit 127", exception.Message, StringComparison.Ordinal);
            Assert.Contains("/missing/git: executable not found", exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            Environment.SetEnvironmentVariable("PATH", previousPath);
        }
    }

    [Fact]
    public void MissingGitExecutableIsInfrastructureWithNativeFailureDetails()
    {
        using var repository = new TemporaryDirectory();
        var missingGit = Path.Combine(repository.Path, "missing-git");
        var gateway = new GitRepositoryGateway(
            repository.Path,
            new ProductionGitProcessRunner(),
            missingGit);

        var exception = Assert.Throws<GitInfrastructureException>(() =>
            gateway.ValidateFrozenReferences(NoReferences()));

        Assert.Equal(GitCommandFailureKind.ExecutableNotFound, exception.Failure.Kind);
        Assert.Null(exception.Failure.ExitCode);
        Assert.NotNull(exception.Failure.NativeErrorCode);
        Assert.Equal(missingGit, exception.Failure.Executable);
        Assert.Contains("rev-parse", exception.Failure.Arguments);
    }

    [Fact]
    public void GitTimeoutIsInfrastructureWithTimeoutClassification()
    {
        // This covers GitRaw translating TimeoutException into the domain Timeout failure.
        // ASSUMED-UNVERIFIED: it does not cover ProductionGitProcessRunner process startup,
        // timeout cancellation, WaitForExitAsync, process-tree kill, or gitTimeout forwarding.
        using var repository = new TemporaryDirectory();
        var gateway = new GitRepositoryGateway(
            repository.Path,
            new ThrowingGitProcessRunner(new TimeoutException("synthetic Git timeout")),
            "git");

        var exception = Assert.Throws<GitInfrastructureException>(() =>
            gateway.ValidateFrozenReferences(NoReferences()));

        Assert.Equal(GitCommandFailureKind.Timeout, exception.Failure.Kind);
        Assert.Null(exception.Failure.ExitCode);
        Assert.Equal("synthetic Git timeout", exception.Failure.Detail);
    }

    [Fact]
    public void GitIoFailureIsInfrastructureWithIoClassification()
    {
        using var repository = new TemporaryDirectory();
        var gateway = new GitRepositoryGateway(
            repository.Path,
            new ThrowingGitProcessRunner(new IOException("synthetic Git pipe read failure")),
            "git");

        var exception = Assert.Throws<GitInfrastructureException>(() =>
            gateway.ValidateFrozenReferences(NoReferences()));

        Assert.Equal(GitCommandFailureKind.Io, exception.Failure.Kind);
        Assert.Null(exception.Failure.ExitCode);
        Assert.Equal("synthetic Git pipe read failure", exception.Failure.Detail);
    }

    [Fact]
    public void RevParseNonzeroExitPreservesExitCodeAndStderr()
    {
        using var repository = new TemporaryDirectory();
        var gateway = new GitRepositoryGateway(
            repository.Path,
            new DelegateGitProcessRunner((_, _) => Output(41, stderr: "rev-parse fixture failure\n")),
            "git");

        var exception = Assert.Throws<GitInfrastructureException>(() =>
            gateway.ValidateFrozenReferences(NoReferences()));

        Assert.Equal(GitCommandFailureKind.NonzeroExit, exception.Failure.Kind);
        Assert.Equal(41, exception.Failure.ExitCode);
        Assert.Equal("rev-parse fixture failure", exception.Failure.StandardError);
        Assert.Equal("rev-parse", exception.Failure.Arguments[0]);
    }

    [Fact]
    public void LsTreeNonzeroExitPreservesExitCodeAndStderr()
    {
        using var repository = new TemporaryDirectory();
        var input = FixtureInput();
        var gateway = new GitRepositoryGateway(
            repository.Path,
            new DelegateGitProcessRunner((arguments, standardInput) => arguments[0] switch
            {
                "cat-file" => BatchCheck(standardInput),
                "ls-tree" => Output(74, stderr: "ls-tree fixture IO failure\n"),
                "rev-parse" when arguments[1] == "--show-object-format" => Output(0, "sha1\n"),
                "rev-parse" => Output(0, input.BaseTreeOid["git-sha1:".Length..] + "\n"),
                _ => throw new InvalidOperationException("unexpected fixture command"),
            }),
            "git");

        var exception = Assert.Throws<GitInfrastructureException>(() =>
            gateway.ValidateFrozenReferences(FrozenLedgerReferenceSet.Create(
                ImmutableArray.Create(input),
                ImmutableArray<string>.Empty)));

        Assert.Equal(GitCommandFailureKind.NonzeroExit, exception.Failure.Kind);
        Assert.Equal(74, exception.Failure.ExitCode);
        Assert.Equal("ls-tree fixture IO failure", exception.Failure.StandardError);
        Assert.Equal("ls-tree", exception.Failure.Arguments[0]);
    }

    [Fact]
    public void EveryReferencedObjectIsValidatedInASingleBatchCheckInvocation()
    {
        var catFileCalls = 0;
        var batchedIds = ImmutableArray<string>.Empty;
        var gateway = new GitRepositoryGateway(
            "/repo",
            new DelegateGitProcessRunner((arguments, standardInput) =>
            {
                if (arguments[0] == "cat-file" && arguments[1] == "--batch-check")
                {
                    catFileCalls++;
                    batchedIds = Encoding.UTF8.GetString(standardInput.Span)
                        .Split('\n', StringSplitOptions.RemoveEmptyEntries)
                        .ToImmutableArray();
                    return BatchCheck(standardInput);
                }

                if (arguments[0] == "rev-parse" && arguments[1] == "--show-object-format")
                {
                    return Output(0, "sha1\n");
                }

                throw new InvalidOperationException("unexpected fixture command " + arguments[0]);
            }),
            "git");

        gateway.ValidateFrozenReferences(FrozenLedgerReferenceSet.Create(
            ImmutableArray<FrozenLedgerInput>.Empty,
            ImmutableArray<string>.Empty,
            ["git-sha1:" + new string('a', 40)],
            ["git-sha1:" + new string('b', 40)],
            ["git-sha1:" + new string('c', 40), "git-sha1:" + new string('d', 40)]));

        // Exactly one process spawn, and every referenced object id — across all three
        // categories — is present in that single batch. A regression that dropped a whole
        // category would leave its ids out of the stdin here.
        Assert.Equal(1, catFileCalls);
        Assert.Equal(
            new[] { new string('a', 40), new string('b', 40), new string('c', 40), new string('d', 40) },
            batchedIds.OrderBy(static id => id, StringComparer.Ordinal).ToArray());
    }

    [Theory]
    [InlineData("OID commit garbage\n")]        // non-decimal size
    [InlineData("OID commit -1\n")]             // signed size
    [InlineData("OID commit 1x\n")]             // trailing junk in size
    [InlineData("OID commit\n")]                // missing size field
    [InlineData("OID\n")]                       // single field
    [InlineData("OID missing extra\n")]         // malformed missing frame
    [InlineData("OID commit 1")]                // missing final newline
    [InlineData("OID commit 1 extra\n")]        // present frame with a trailing field
    [InlineData("OID  commit 1\n")]             // repeated space between fields
    [InlineData("OID commit 1\nOID commit 1\n")] // more lines than inputs
    [InlineData("")]                            // empty output
    [InlineData("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb commit 1\n")] // echoed oid mismatch
    public void MalformedBatchCheckSuccessFrameFailsClosed(string template)
    {
        var oid = new string('a', 40);
        var output = template.Replace("OID", oid, StringComparison.Ordinal);
        var gateway = new GitRepositoryGateway(
            "/repo",
            new DelegateGitProcessRunner((arguments, _) => arguments[0] switch
            {
                "cat-file" => Output(0, output),
                "rev-parse" when arguments[1] == "--show-object-format" => Output(0, "sha1\n"),
                _ => throw new InvalidOperationException("unexpected fixture command"),
            }),
            "git");

        var exception = Assert.Throws<GitInfrastructureException>(() =>
            gateway.ValidateFrozenReferences(FrozenLedgerReferenceSet.Create(
                ImmutableArray<FrozenLedgerInput>.Empty,
                ImmutableArray<string>.Empty,
                ["git-sha1:" + oid],
                ImmutableArray<string>.Empty,
                ImmutableArray<string>.Empty)));

        Assert.Equal(GitCommandFailureKind.InvalidOutput, exception.Failure.Kind);
    }

    [Fact]
    public void ValidSizeInBatchCheckSuccessFrameIsAccepted()
    {
        var oid = new string('a', 40);
        var gateway = new GitRepositoryGateway(
            "/repo",
            new DelegateGitProcessRunner((arguments, _) => arguments[0] switch
            {
                "cat-file" => Output(0, oid + " commit 0\n"),
                "rev-parse" when arguments[1] == "--show-object-format" => Output(0, "sha1\n"),
                _ => throw new InvalidOperationException("unexpected fixture command"),
            }),
            "git");

        gateway.ValidateFrozenReferences(FrozenLedgerReferenceSet.Create(
            ImmutableArray<FrozenLedgerInput>.Empty,
            ImmutableArray<string>.Empty,
            ["git-sha1:" + oid],
            ImmutableArray<string>.Empty,
            ImmutableArray<string>.Empty));
    }

    [Fact]
    public void BatchCheckMissingLineIsMissingObjectRejection()
    {
        var oid = "git-sha1:" + new string('a', 40);
        var gateway = new GitRepositoryGateway(
            "/repo",
            new DelegateGitProcessRunner((arguments, standardInput) => arguments[0] switch
            {
                "cat-file" => Output(0, oid["git-sha1:".Length..] + " missing\n"),
                "rev-parse" when arguments[1] == "--show-object-format" => Output(0, "sha1\n"),
                _ => throw new InvalidOperationException("unexpected fixture command"),
            }),
            "git");

        var exception = Assert.Throws<FrozenReferenceRejectionException>(() =>
            gateway.ValidateFrozenReferences(FrozenLedgerReferenceSet.Create(
                ImmutableArray<FrozenLedgerInput>.Empty,
                ImmutableArray<string>.Empty,
                [oid],
                ImmutableArray<string>.Empty,
                ImmutableArray<string>.Empty)));

        Assert.Equal(FrozenReferenceRejectionKind.MissingObject, exception.Kind);
        Assert.Contains("is not a reachable commit", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BatchCheckWrongTypeIsWrongObjectTypeRejection()
    {
        var oid = "git-sha1:" + new string('a', 40);
        var gateway = new GitRepositoryGateway(
            "/repo",
            new DelegateGitProcessRunner((arguments, standardInput) => arguments[0] switch
            {
                "cat-file" => Output(0, oid["git-sha1:".Length..] + " blob 12\n"),
                "rev-parse" when arguments[1] == "--show-object-format" => Output(0, "sha1\n"),
                _ => throw new InvalidOperationException("unexpected fixture command"),
            }),
            "git");

        var exception = Assert.Throws<FrozenReferenceRejectionException>(() =>
            gateway.ValidateFrozenReferences(FrozenLedgerReferenceSet.Create(
                ImmutableArray<FrozenLedgerInput>.Empty,
                ImmutableArray<string>.Empty,
                [oid],
                ImmutableArray<string>.Empty,
                ImmutableArray<string>.Empty)));

        Assert.Equal(FrozenReferenceRejectionKind.WrongObjectType, exception.Kind);
        Assert.Contains("has type blob; expected commit", exception.Message, StringComparison.Ordinal);
    }

    private static FrozenLedgerReferenceSet NoReferences() =>
        FrozenLedgerReferenceSet.Create(
            ImmutableArray<FrozenLedgerInput>.Empty,
            ImmutableArray<string>.Empty);

    private static FrozenLedgerInput FixtureInput() =>
        new(
            "git-sha1:" + new string('a', 40),
            "git-sha1:" + new string('b', 40),
            "git-sha1:" + new string('c', 40),
            "D5/S0/Carrier/A.lean",
            ImmutableArray.Create("git-sha1:" + new string('d', 40)));

    private static string ObjectType(string oid) => oid[0] switch
    {
        'a' => "commit",
        'b' => "tree",
        'c' or 'd' => "blob",
        _ => throw new InvalidOperationException("unexpected fixture OID"),
    };

    private static ProcessOutput Output(int exitCode, string output = "", string stderr = "") =>
        new(exitCode, Encoding.UTF8.GetBytes(output), Encoding.UTF8.GetBytes(stderr));

    private sealed class ThrowingGitProcessRunner(Exception exception) : IGitProcessRunner
    {
        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout,
            int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default) => throw exception;
    }

    private sealed class DelegateGitProcessRunner(
        Func<IReadOnlyList<string>, ReadOnlyMemory<byte>, ProcessOutput> run) : IGitProcessRunner
    {
        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout,
            int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default) => run(arguments, standardInput);
    }

    // Reproduce `git cat-file --batch-check`: one header line per stdin object id,
    // in input order, using the fixture's first-character type mapping.
    private static ProcessOutput BatchCheck(ReadOnlyMemory<byte> standardInput)
    {
        var ids = Encoding.UTF8.GetString(standardInput.Span)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);
        var builder = new StringBuilder();
        foreach (var id in ids)
        {
            builder.Append(id).Append(' ').Append(ObjectType(id)).Append(" 1\n");
        }

        return Output(0, builder.ToString());
    }
}

internal static class FrozenGitProcessEnvironmentCollection
{
    internal const string Name = "Frozen Git process environment";
}

[CollectionDefinition(FrozenGitProcessEnvironmentCollection.Name, DisableParallelization = true)]
public sealed class FrozenGitProcessEnvironmentCollectionDefinition;

namespace StrataLint.ArchitectureTests;

/// <summary>
/// Pins the recognized-shape early-feedback boundary of <see cref="RemoteStateIndependencePolicy"/>.
/// These tests do not claim execution-path completeness; CI remote capability stripping provides
/// the post-checkout strip step, which eliminates name-based remote resolution but is not a
/// remote-unreachability guarantee; see CLAUDE.md for the measured residuals.
/// </summary>
public sealed class RemoteStateEarlyFeedbackPolicyTests
{
    private static readonly string RepositoryRoot = RepositoryLayout.FindRoot();
    private static readonly IReadOnlyDictionary<string, string> InertLiteralSources =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["tools/tests/StrataLint.Tests/Commands/WorktreeCommandTests.cs"] = File.ReadAllText(
                Path.Combine(RepositoryRoot, "tools/tests/StrataLint.Tests/Commands/WorktreeCommandTests.cs")),
            ["tools/tests/StrataLint.Tests/Commands/CleanLanes/CleanLanesCommandTests.cs"] = File.ReadAllText(
                Path.Combine(RepositoryRoot, "tools/tests/StrataLint.Tests/Commands/CleanLanes/CleanLanesCommandTests.cs")),
            ["tools/tests/StrataLint.Tests/Digestion/Sources/DigestionSourceConflictMarkerTests.cs"] = File.ReadAllText(
                Path.Combine(RepositoryRoot, "tools/tests/StrataLint.Tests/Digestion/Sources/DigestionSourceConflictMarkerTests.cs")),
        };

    [Fact]
    public void RecognizedRealRepositoryRemoteRevisionProducesEarlyFeedbackWithFileAndLineWitness()
    {
        const string source = """
            class RemoteDependentTests
            {
                void ReadsMovingBase()
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    var repository = new GitRepositoryGateway(checkout);
                    repository.ReadRevision("origin/dev");
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("RemoteDependentTests.cs", source)));

        Assert.Equal("RemoteDependentTests.cs:7", finding.Location);
        Assert.Equal("disallowed revision", finding.Operation);
    }

    [Fact]
    public void RealRepositoryRevisionMustBeProvablyLocalOrContentAddressed()
    {
        const string source = """
            class DynamicRevisionTests
            {
                void ReadsUnknownRevision(string revision)
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    new GitRepositoryGateway(checkout).ReadRevision(revision);
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("DynamicRevisionTests.cs", source)));

        Assert.Equal("DynamicRevisionTests.cs:6", finding.Location);
        Assert.Contains("not head or base", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ComposedRemoteTrackingNamespaceIsRejected()
    {
        const string source = """
            class EquivalentRemoteTests
            {
                void ReadsEquivalentRemote()
                {
                    const string remoteNamespace = "refs/remotes/";
                    const string revision = remoteNamespace + "upstream/dev";
                    var checkout = TestRepositoryLayout.FindRoot();
                    new GitRepositoryGateway(checkout).ReadRevision(revision);
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("EquivalentRemoteTests.cs", source)));

        Assert.Equal("EquivalentRemoteTests.cs:8", finding.Location);
    }

    [Theory]
    [InlineData("refs/heads/dev")]
    [InlineData("refs/tags/v1")]
    [InlineData("HEAD~1")]
    [InlineData("0123456789012345678901234567890123456789")]
    public void RealRepositoryOnlyHeadAndBaseReferencesAreAllowed(string revision)
    {
        var source = $$"""
            class OtherRevisionTests
            {
                void ReadsOtherRevision()
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    new GitRepositoryGateway(checkout).ReadRevision("{{revision}}");
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("OtherRevisionTests.cs", source)));

        Assert.Equal("OtherRevisionTests.cs:6", finding.Location);
        Assert.Contains("not head or base", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RealRepositoryFetchIsRejected()
    {
        const string source = """
            class FetchTests
            {
                void FetchesMovingBase()
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    ReviewRegressionTests.RunGit(checkout, "fetch", "origin", "dev");
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("FetchTests.cs", source)));

        Assert.Equal("FetchTests.cs:6", finding.Location);
        Assert.Equal("git fetch", finding.Operation);
    }

    [Fact]
    public void RealRepositoryBoundedProcessFetchIsRejected()
    {
        const string source = """
            class ProcessFetchTests
            {
                void FetchesMovingBase()
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    BoundedProcessRunner.Run("git", ["fetch", "origin", "dev"], checkout);
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("ProcessFetchTests.cs", source)));

        Assert.Equal("ProcessFetchTests.cs:6", finding.Location);
        Assert.Equal("git fetch", finding.Operation);
    }

    [Fact]
    public void RealRepositoryBoundedProcessUnknownArgumentsFailClosed()
    {
        const string source = """
            class ProcessGitTests
            {
                void ReadsUnknownRevision(string[] arguments)
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    BoundedProcessRunner.Run("git", arguments, checkout);
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("ProcessGitTests.cs", source)));

        Assert.Equal("ProcessGitTests.cs:6", finding.Location);
        Assert.Equal("git command", finding.Operation);
    }

    [Fact]
    public void FixtureRepositoryBoundedProcessFetchStaysGreen()
    {
        const string source = """
            class FixtureProcessFetchTests
            {
                void FetchesFixtureRemote()
                {
                    using var fixture = new TemporaryDirectory();
                    BoundedProcessRunner.Run("git", ["fetch", "origin", "dev"], fixture.Path);
                }
            }
            """;

        Assert.Empty(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("FixtureProcessFetchTests.cs", source)));
    }

    [Fact]
    public void RealRepositoryProcessStartInfoFetchIsRejected()
    {
        const string source = """
            class ProcessStartInfoFetchTests
            {
                void FetchesMovingBase()
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    var startInfo = new ProcessStartInfo("git") { WorkingDirectory = checkout };
                    startInfo.ArgumentList.Add("fetch");
                    Process.Start(startInfo);
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("ProcessStartInfoFetchTests.cs", source)));

        Assert.Equal("ProcessStartInfoFetchTests.cs:6", finding.Location);
        Assert.Equal("git fetch", finding.Operation);
    }

    [Fact]
    public void LiveRepositoryHttpApiIsRejectedButLoopbackFixtureStaysGreen()
    {
        const string remoteSource = """
            class RemoteApiTests
            {
                void QueriesLiveRepository()
                {
                    var client = new HttpClient();
                    client.GetStringAsync("https://api.github.com/repos/example/project");
                }
            }
            """;
        const string loopbackSource = """
            class LoopbackApiTests
            {
                void QueriesFixture()
                {
                    var client = new HttpClient();
                    client.GetStringAsync("http://127.0.0.1:8080/fixture");
                }
            }
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("RemoteApiTests.cs", remoteSource)));
        Assert.Equal("RemoteApiTests.cs:6", finding.Location);
        Assert.Equal("remote API", finding.Operation);
        Assert.Empty(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("LoopbackApiTests.cs", loopbackSource)));
    }

    [Fact]
    public void FixtureRepositoryMayResolveRemoteTrackingRevision()
    {
        const string source = """
            class FixtureRepositoryTests
            {
                void ReadsFixtureRemote()
                {
                    using var fixture = new TemporaryDirectory();
                    new GitRepositoryGateway(fixture.Path).ReadRevision("origin/dev");
                    ReviewRegressionTests.RunGit(fixture.Path, "fetch", "origin", "dev");
                }
            }
            """;

        Assert.Empty(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("FixtureRepositoryTests.cs", source)));
    }

    [Fact]
    public void RealRepositoryWorkingTreeAndHeadReadsStayGreen()
    {
        const string source = """
            class WorkingTreeTests
            {
                void ReadsCheckout()
                {
                    var checkout = TestRepositoryLayout.FindRoot();
                    var repository = new GitRepositoryGateway(checkout);
                    repository.ReadCurrent();
                    repository.ReadRevision("HEAD");
                    repository.ReadRevision("HEAD^1");
                }
            }
            """;

        Assert.Empty(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("WorkingTreeTests.cs", source)));
    }

    [Theory]
    [InlineData("tools/tests/StrataLint.Tests/Commands/WorktreeCommandTests.cs")]
    [InlineData("tools/tests/StrataLint.Tests/Commands/CleanLanes/CleanLanesCommandTests.cs")]
    [InlineData("tools/tests/StrataLint.Tests/Digestion/Sources/DigestionSourceConflictMarkerTests.cs")]
    public void InertRemoteShapedLiteralsInExistingTestsStayGreen(string relativePath)
    {
        var source = InertLiteralSources[relativePath];

        Assert.Empty(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource(relativePath, source)));
    }

    [Fact]
    public void RepositoryTestsContainNoRecognizedRemoteDependencyShapes()
    {
        var findings = RemoteStateIndependencePolicy.InspectRepository(RepositoryRoot);

        Assert.Empty(findings);
    }
}

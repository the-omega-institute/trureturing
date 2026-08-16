namespace StrataLint.ArchitectureTests;

public sealed class RemoteStateIndependencePolicyTests
{
    private static readonly string RepositoryRoot = RepositoryLayout.FindRoot();
    private static readonly IReadOnlyDictionary<string, string> InertLiteralSources =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["tools/tests/StrataLint.Tests/Commands/WorktreeCommandTests.cs"] = File.ReadAllText(
                Path.Combine(RepositoryRoot, "tools/tests/StrataLint.Tests/Commands/WorktreeCommandTests.cs")),
            ["tools/tests/StrataLint.Tests/Commands/CleanLanesCommandTests.cs"] = File.ReadAllText(
                Path.Combine(RepositoryRoot, "tools/tests/StrataLint.Tests/Commands/CleanLanesCommandTests.cs")),
            ["tools/tests/StrataLint.Tests/Digestion/Sources/DigestionSourceConflictMarkerTests.cs"] = File.ReadAllText(
                Path.Combine(RepositoryRoot, "tools/tests/StrataLint.Tests/Digestion/Sources/DigestionSourceConflictMarkerTests.cs")),
        };

    [Fact]
    public void RealRepositoryRemoteRevisionIsRejectedWithFileAndLineWitness()
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
        Assert.Equal("remote revision", finding.Operation);
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
        Assert.Contains("not provably local", finding.Message, StringComparison.Ordinal);
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
                }
            }
            """;

        Assert.Empty(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource("WorkingTreeTests.cs", source)));
    }

    [Theory]
    [InlineData("tools/tests/StrataLint.Tests/Commands/WorktreeCommandTests.cs")]
    [InlineData("tools/tests/StrataLint.Tests/Commands/CleanLanesCommandTests.cs")]
    [InlineData("tools/tests/StrataLint.Tests/Digestion/Sources/DigestionSourceConflictMarkerTests.cs")]
    public void InertRemoteShapedLiteralsInExistingTestsStayGreen(string relativePath)
    {
        var source = InertLiteralSources[relativePath];

        Assert.Empty(RemoteStateIndependencePolicy.InspectTestSource(
            new RemoteStateSource(relativePath, source)));
    }

    [Fact]
    public void CheckoutMayBringTreeInButPostCheckoutFetchIsRejected()
    {
        const string workflow = """
            jobs:
              test:
                steps:
                  - uses: actions/checkout@v4
                    with:
                      ref: origin/dev
                  - name: Fetch moving base
                    run: git -C candidate fetch --no-tags origin "$base"
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectWorkflowSource(
            new RemoteStateSource(".github/workflows/sample.yml", workflow)));

        Assert.Equal(".github/workflows/sample.yml:8", finding.Location);
        Assert.Equal("git fetch", finding.Operation);
    }

    [Fact]
    public void PostCheckoutLocalGitReadsStayGreen()
    {
        const string workflow = """
            jobs:
              test:
                steps:
                  - uses: actions/checkout@v4
                  - name: Inspect checked out objects
                    run: |
                      git rev-parse HEAD
                      git diff --name-only "$base_sha" "$head_sha"
                      git diff -- path/to/working-tree-file
            """;

        Assert.Empty(RemoteStateIndependencePolicy.InspectWorkflowSource(
            new RemoteStateSource(".github/workflows/local.yml", workflow)));
    }

    [Fact]
    public void QuotedCommandTextDoesNotCountAsRemoteAccess()
    {
        const string workflow = """
            jobs:
              test:
                steps:
                  - uses: actions/checkout@v4
                  - run: printf '%s\n' 'git fetch origin dev'
            """;

        Assert.Empty(RemoteStateIndependencePolicy.InspectWorkflowSource(
            new RemoteStateSource(".github/workflows/text.yml", workflow)));
    }

    [Fact]
    public void PostCheckoutRemoteApiQueryIsRejected()
    {
        const string workflow = """
            jobs:
              test:
                steps:
                  - uses: actions/checkout@v4
                  - name: Query live pull request
                    run: gh api repos/example/project/pulls/1
            """;

        var finding = Assert.Single(RemoteStateIndependencePolicy.InspectWorkflowSource(
            new RemoteStateSource(".github/workflows/api.yml", workflow)));

        Assert.Equal(".github/workflows/api.yml:6", finding.Location);
        Assert.Equal("remote API", finding.Operation);
    }

    [Fact]
    public void RepositoryTestsAndPostCheckoutWorkflowsAreRemoteStateIndependent()
    {
        var findings = RemoteStateIndependencePolicy.InspectRepository(RepositoryRoot);

        Assert.Empty(findings);
    }
}

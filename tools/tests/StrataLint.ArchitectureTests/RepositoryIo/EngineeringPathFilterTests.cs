using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

public sealed class EngineeringPathFilterTests
{
    [Fact]
    public void Pr2343BlueprintAndD5DescribeInputsWakeEngineering()
    {
        var closure = EngineeringInputDeriver.DeriveRepository(RepositoryLayout.FindRoot());

        var decision = EngineeringScopePolicy.Evaluate(
            [
                "Blueprint/D5/S3/Synthetic/NewTheorem.scribe.cs",
                "D5/S3/Synthetic/NewTheorem.lean",
            ],
            closure);

        Assert.True(decision.Run);
        Assert.Equal(2, decision.MatchedPaths.Length);
    }

    [Fact]
    public void EveryDerivedTestRepositoryInputWakesEngineering()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var closure = EngineeringInputDeriver.DeriveRepository(repositoryRoot);
        var declaredReads = ScribeTestMapDeriver.DeriveRepository(repositoryRoot).Methods
            .SelectMany(static method => method.Paths)
            .Distinct(StringComparer.Ordinal)
            .ToArray();

        Assert.NotEmpty(declaredReads);
        Assert.All(
            declaredReads,
            input =>
            {
                var decision = EngineeringScopePolicy.Evaluate([input], closure);
                Assert.True(decision.Run, $"derived test input did not wake engineering: {input}");
                Assert.Contains(input, decision.MatchedPaths);
            });
    }

    [Fact]
    public void NewExternalProjectInputIsDerivedWithoutEditingScopePolicy()
    {
        var closure = EngineeringInputDeriver.DeriveProjectInputs(
            "/repo",
            [
                new EngineeringProjectInput(
                    "tools/Product/Product.csproj",
                    "<Project><ItemGroup><Compile Include=\"../../NewCorpus/**/*.fixture.cs\" /></ItemGroup></Project>"),
            ],
            repositoryReads: []);

        var decision = EngineeringScopePolicy.Evaluate(
            ["NewCorpus/example/new.fixture.cs"],
            closure);

        Assert.True(decision.Run);
        Assert.Equal("NewCorpus/example/new.fixture.cs", Assert.Single(decision.MatchedPaths));
    }

    [Fact]
    public void ProvenDisjointChangeSkipsWhenConsumerDerivationIsComplete()
    {
        var closure = EngineeringInputDeriver.DeriveProjectInputs(
            "/repo",
            [new EngineeringProjectInput("tools/Product/Product.csproj", "<Project />")],
            repositoryReads: []);

        var decision = EngineeringScopePolicy.Evaluate(
            ["ReferenceOnlyScopeFixture/notes.md"],
            closure);

        Assert.False(decision.Run);
        Assert.Empty(decision.MatchedPaths);
        Assert.Equal(EngineeringScopeReason.ProvenDisjoint, decision.Reason);
    }

    [Fact]
    public void RepositoryUnknownConsumerInputsFailClosed()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var map = ScribeTestMapDeriver.DeriveRepository(repositoryRoot);
        var closure = EngineeringInputDeriver.DeriveRepository(repositoryRoot);

        Assert.Contains(map.Methods, static method => method.IsUnknown);
        Assert.False(closure.IsComplete);
        Assert.Contains("test consumers", closure.IncompleteReason, StringComparison.Ordinal);

        var decision = EngineeringScopePolicy.Evaluate(
            ["ReferenceOnlyScopeFixture/notes.md"],
            closure);

        Assert.True(decision.Run);
        Assert.Equal(EngineeringScopeReason.IncompleteDerivation, decision.Reason);
    }

    [Fact]
    public void IncompleteConsumerDerivationFailsClosed()
    {
        var closure = new EngineeringInputClosure(
            [],
            [],
            IsComplete: false,
            IncompleteReason: "synthetic derivation failure");

        var decision = EngineeringScopePolicy.Evaluate(
            ["ReferenceOnlyScopeFixture/notes.md"],
            closure);

        Assert.True(decision.Run);
        Assert.Equal(EngineeringScopeReason.IncompleteDerivation, decision.Reason);
    }

    [Fact]
    public void WorkflowDelegatesExternalScopeToConsumerDerivationInsteadOfAPathList()
    {
        var script = ScopeScript();

        Assert.DoesNotContain("engineering_triggers", script, StringComparison.Ordinal);
        Assert.Contains(
            "git -C candidate ls-tree -r --name-only -z \"$base_sha\" -- '*.sln'",
            script,
            StringComparison.Ordinal);
        Assert.Contains("StrataLint.EngineeringScope.csproj", script, StringComparison.Ordinal);
        Assert.Contains("--changes-file", script, StringComparison.Ordinal);
        Assert.Contains("--result-file", script, StringComparison.Ordinal);
        Assert.Contains("fails closed", script, StringComparison.OrdinalIgnoreCase);
    }

    private static string ScopeScript()
    {
        var workflow = File.ReadAllText(
            Path.Combine(RepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var root = (YamlMappingNode)stream.Documents[0].RootNode;
        var jobs = (YamlMappingNode)root.Children[new YamlScalarNode("jobs")];
        var engineering = (YamlMappingNode)jobs.Children[new YamlScalarNode("candidate-engineering")];
        var steps = (YamlSequenceNode)engineering.Children[new YamlScalarNode("steps")];
        var scope = steps.Children.OfType<YamlMappingNode>().Single(step =>
            step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        return ((YamlScalarNode)scope.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
    }
}

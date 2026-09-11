using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class RegisteredCompileSourcesTests
{
    [Fact]
    public void SharedLinkedTestHasSeparateRegisteredDebtIdentitiesInColocatedProjects()
    {
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest(
            new EngineeringProjectFixture("checks/one.csproj", "One", "cross-cutting-test", true, ["shared/Linked.cs"]),
            new EngineeringProjectFixture("checks/two.csproj", "Two", "cross-cutting-test", true, ["shared/Linked.cs"])))!;
        manifest["projects"]![0]!["test_partition"] = "first-suite";
        manifest["projects"]![1]!["test_partition"] = "second-suite";
        var snapshot = Snapshot(
            (EngineeringRegistrationFixture.Path, manifest.ToJsonString()),
            ("checks/one.csproj", "<Project />"), ("checks/two.csproj", "<Project />"),
            ("shared/Linked.cs", "public class Linked { [Xunit.Fact] public void Runs() { } }"));

        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot, _ =>
            [.. ScribeMetadataReferenceResolver.PlatformReferences().Select(reference => reference.Display!),
                typeof(Xunit.FactAttribute).Assembly.Location]);

        Assert.Equal(["first-suite", "second-suite"], map.Methods.Select(method => method.PartitionKey));
        Assert.All(map.Methods, method => Assert.Equal("Linked.Runs", method.Id));
        Assert.All(map.Methods, method => Assert.Equal("shared/Linked.cs", method.SourcePath));
        Assert.All(map.Methods, method => Assert.False(method.IsUnknown));
    }

    [Fact]
    public void LinkedSourceBelongsToBothRegisteredProjectsAndExcludedSourceToNeither()
    {
        var projects = new[]
        {
            new EngineeringProjectFixture("a/a.csproj", "First", "cross-cutting-test", true,
                ["a/**/*.cs", "shared/**/*.cs"], ["shared/Excluded.cs"]),
            new EngineeringProjectFixture("b/b.csproj", "Second", "cross-cutting-test", true,
                ["b/**/*.cs", "shared/**/*.cs"], ["shared/Excluded.cs"]),
        };
        var snapshot = Snapshot(
            (EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(projects)),
            ("a/a.csproj", "<Project />"), ("b/b.csproj", "<Project />"),
            ("a/Local.cs", "class Local {}"), ("shared/Linked.cs", "class Linked {}"),
            ("shared/Excluded.cs", "class Excluded {}"));
        var seen = new List<ScribeCompilationProject>();
        ScribeTestMapDeriver.DeriveSnapshot(snapshot, items =>
        {
            seen.AddRange(items);
            return [];
        });
        var first = Assert.Single(seen.Where(project => project.AssemblyName == "First").DistinctBy(project => project.Path));
        var second = Assert.Single(seen.Where(project => project.AssemblyName == "Second").DistinctBy(project => project.Path));
        Assert.Equal(["a/Local.cs", "shared/Linked.cs"], first.Sources.Select(source => source.Path));
        Assert.Equal(["shared/Linked.cs"], second.Sources.Select(source => source.Path));
    }

    [Fact]
    public void MissingLiteralLinkedSourceFailsWithoutEvaluatingProject()
    {
        var snapshot = Snapshot(
            (EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture("p/p.csproj", "P", "test-support", false, ["shared/Missing.cs"]))),
            ("p/p.csproj", "<Project />"));
        Assert.Throws<InvalidDataException>(() => ScribeTestMapDeriver.DeriveSnapshot(snapshot, _ => []));
    }

    [Fact]
    public void SourceOutsideEveryRegisteredIncludeOrExcludeFails()
    {
        var snapshot = Snapshot(
            (EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture("p/p.csproj", "P", "test-support", false, ["p/*.cs"]))),
            ("p/p.csproj", "<Project />"), ("elsewhere/Unowned.cs", "class Unowned {}"));
        Assert.Throws<InvalidDataException>(() => ScribeTestMapDeriver.DeriveSnapshot(snapshot, _ => []));
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(file => RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}

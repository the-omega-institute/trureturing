using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class RegisteredCompileSourcesTests
{
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
        var sources = Sources(snapshot);
        Assert.Equal(["a/Local.cs", "shared/Linked.cs"], sources["a/a.csproj"].Select(source => source.Path));
        Assert.Equal(["shared/Linked.cs"], sources["b/b.csproj"].Select(source => source.Path));
    }

    [Fact]
    public void MissingLiteralLinkedSourceFailsWithoutEvaluatingProject()
    {
        var snapshot = Snapshot(
            (EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture("p/p.csproj", "P", "test-support", false, ["shared/Missing.cs"]))),
            ("p/p.csproj", "<Project />"));
        Assert.Throws<InvalidDataException>(() => Sources(snapshot));
    }

    [Fact]
    public void SourceOutsideEveryRegisteredIncludeOrExcludeFails()
    {
        var snapshot = Snapshot(
            (EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new EngineeringProjectFixture("p/p.csproj", "P", "test-support", false, ["p/*.cs"]))),
            ("p/p.csproj", "<Project />"), ("elsewhere/Unowned.cs", "class Unowned {}"));
        Assert.Throws<InvalidDataException>(() => Sources(snapshot));
    }

    private static IReadOnlyDictionary<string, IReadOnlyList<EngineeringSource>> Sources(RepositorySnapshot snapshot) =>
        EngineeringProjectRegistry.Read(snapshot).Sources(snapshot.Files.Values
            .Select(file => new EngineeringSource(file.Path.Value, file.Text)).ToArray());

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(file => RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}

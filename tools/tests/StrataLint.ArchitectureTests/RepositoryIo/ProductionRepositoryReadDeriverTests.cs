namespace StrataLint.ArchitectureTests;

public sealed class ProductionRepositoryReadDeriverTests
{
    [Fact]
    public void RepositoryReadersAreDerivedThroughDirectTransitiveAndExternalCalls()
    {
        var sources = new[]
        {
            new RepositoryReadSource("Product", "Direct.cs", "class Direct { void Read(string path) => File.ReadAllText(path); }"),
            new RepositoryReadSource("Product", "Transitive.cs", "class Transitive { void Read(string path) => Direct.Read(path); }"),
            new RepositoryReadSource("Product", "External.cs", "class External { void Read(string repositoryRoot) => ThirdParty.Load(repositoryRoot); }"),
            new RepositoryReadSource("Product", "Pure.cs", "class Pure { int Count(string text) => text.Length; }"),
        };

        var readers = ProductionRepositoryReadDeriver.DeriveReaderTypes(sources);

        Assert.Contains("Direct", readers);
        Assert.Contains("Transitive", readers);
        Assert.Contains("External", readers);
        Assert.DoesNotContain("Pure", readers);
    }

}

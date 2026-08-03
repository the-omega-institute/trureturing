namespace StrataLint.ArchitectureTests;

public sealed class PapergenLedgerReferenceTripwireTests
{
    [Fact]
    public void NoLedgerReplayTypeIsNamedAlongPapergensDirectTypeReferences()
    {
        var root = RepositoryLayout.FindRoot();

        var findings = PapergenLedgerReferenceTripwire.NamedReplayTypes(
            PapergenLedgerReferenceTripwire.CliDirectory(root),
            PapergenLedgerReferenceTripwire.PapergenDirectory(root));

        Assert.Empty(findings);
    }

    /// Empty findings prove nothing on their own: pointing the locator at any directory holding no
    /// C# -- the repository has several -- satisfies the rule above while walking nothing at all,
    /// so one line could switch this off in silence. The scope is asserted independently of the
    /// policy that consumes it.
    [Fact]
    public void ThePapergenScopeIsTheCanonicalCommandDirectoryAndHoldsSources()
    {
        var root = RepositoryLayout.FindRoot();

        var directory = PapergenLedgerReferenceTripwire.PapergenDirectory(root);

        Assert.Equal(
            Path.Combine(root, "Meta", "StrataLint", "StrataLint.Cli", "Commands", "Papergen"),
            directory);
        Assert.NotEmpty(Directory.EnumerateFiles(directory, "*.cs", SearchOption.AllDirectories));
    }

    /// The walk starts at Papergen's own sources, and a listed name written there is the first
    /// thing it is supposed to report. Without this, an implementation that reports only for
    /// declarations it resolved on the way -- never for the bodies it started from -- passes every
    /// other test here while Papergen writing DagLedgerLoader itself stays green.
    [Fact]
    public void AListedTypeNamedInPapergenItselfIsReported()
    {
        var temporary = Directory.CreateTempSubdirectory("papergen-tripwire-");
        try
        {
            var papergen = Path.Combine(temporary.FullName, "Commands", "Papergen");
            Directory.CreateDirectory(papergen);
            File.WriteAllText(
                Path.Combine(papergen, "Consumer.cs"),
                """
                internal static class Consumer
                {
                    internal static object Resolve(byte[] bytes) => DagLedgerLoader.Load(bytes);
                }
                """);

            var findings = PapergenLedgerReferenceTripwire.NamedReplayTypes(
                temporary.FullName,
                papergen);

            Assert.Equal(["Consumer.cs: DagLedgerLoader"], findings);
        }
        finally
        {
            Directory.Delete(temporary.FullName, recursive: true);
        }
    }

    /// The reason the walk leaves Papergen's own directory at all: a helper elsewhere in the same
    /// assembly, called from Papergen, is the cheap way to rebuild the answer while every listed
    /// name sits outside Papergen's files. Papergen and the helper are in separate directories
    /// here, which is what makes this the case that fails if the walk is narrowed back to
    /// Papergen's own sources.
    [Fact]
    public void AHelperOutsidePapergenIsReachedThroughTheTypeItsCallerNames()
    {
        var temporary = Directory.CreateTempSubdirectory("papergen-tripwire-");
        try
        {
            var cli = temporary.FullName;
            var papergen = Path.Combine(cli, "Commands", "Papergen");
            Directory.CreateDirectory(papergen);
            File.WriteAllText(
                Path.Combine(cli, "Commands", "LedgerReplayHelper.cs"),
                """
                internal static class LedgerReplayHelper
                {
                    internal static object Replay(byte[] bytes) => DagLedgerLoader.Load(bytes);
                }
                """);
            File.WriteAllText(
                Path.Combine(papergen, "Consumer.cs"),
                """
                internal static class Consumer
                {
                    internal static object Resolve(byte[] bytes) => LedgerReplayHelper.Replay(bytes);
                }
                """);

            var findings = PapergenLedgerReferenceTripwire.NamedReplayTypes(cli, papergen);

            Assert.Equal(["LedgerReplayHelper.cs (LedgerReplayHelper): DagLedgerLoader"], findings);
        }
        finally
        {
            Directory.Delete(temporary.FullName, recursive: true);
        }
    }

    /// The sample below carries no namespace declaration: the parser does not need one to find
    /// identifiers, and the repository's namespace rule counts declarations in a file's text, so an
    /// embedded one would be read as this file declaring a second namespace.
    /// Papergen's own source explains in prose which types it must not name. A detector that read
    /// text rather than syntax would report those comments and force the boundary to be documented
    /// somewhere it cannot be read.
    [Fact]
    public void ListedNamesInCommentsAndStringsAreNotReferences()
    {
        var temporary = Directory.CreateTempSubdirectory("papergen-tripwire-");
        try
        {
            File.WriteAllText(
                Path.Combine(temporary.FullName, "Documented.cs"),
                """
                // Never call DagLedgerLoader here: the ledger is prepared elsewhere.
                internal static class Documented
                {
                    internal const string Note = "FrozenLedger.ValidateHistory is not ours to call.";
                }
                """);

            var findings = PapergenLedgerReferenceTripwire.NamedReplayTypes(
                temporary.FullName,
                temporary.FullName);

            Assert.Empty(findings);
        }
        finally
        {
            Directory.Delete(temporary.FullName, recursive: true);
        }
    }
}

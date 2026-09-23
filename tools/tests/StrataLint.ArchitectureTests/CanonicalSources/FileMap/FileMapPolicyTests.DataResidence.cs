using StrataLint.Cli;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void CommittedDataFixturesRespectTheProgramResidenceBoundary()
    {
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var findings = FileMapPolicy.InspectDirectoryKinds(manifest, FileMapPolicy.TrackedPaths(root));

        Assert.DoesNotContain(findings,
            finding => finding.Code == "FILEMAP-DATA-RESIDENCE");
    }
}

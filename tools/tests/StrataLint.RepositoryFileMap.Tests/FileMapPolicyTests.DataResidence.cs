using StrataLint.FileMap;
using StrataLint.Scribe;

namespace StrataLint.RepositoryFileMap.Tests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void CommittedDataFixturesRespectTheProgramResidenceBoundary()
    {
        var root = TestRepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var findings = FileMapPolicy.InspectDirectoryKinds(manifest, FileMapPolicy.TrackedPaths(root));

        Assert.DoesNotContain(findings,
            finding => finding.Code == "FILEMAP-DATA-RESIDENCE");
    }
}

using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class TruthExportProjectionTests
{
    private const string Commit = "1111111111111111111111111111111111111111";
    private const string Tree = "2222222222222222222222222222222222222222";
    private const string LeanReportDigest =
        "sha256:3333333333333333333333333333333333333333333333333333333333333333";

    [Fact]
    public void ProjectMapsFrozenMaterialAndCanonicalizesPrerequisites()
    {
        var repoPath = "D5/S0/Carrier/Alpha.lean";
        var frozenNodeId = Sha("frozen:" + repoPath);
        var prerequisiteA = "sha256:" + new string('a', 64);
        var prerequisiteB = "sha256:" + new string('b', 64);
        var material = new FrozenNodeMaterial(
            RepoPath.CreateKnown(repoPath),
            ImmutableArray.Create(
                new FrozenDeclarationStatement(
                    "nk-two", "theorem", StatementId.Create(Sha("statement:two"))),
                new FrozenDeclarationStatement(
                    "nk-one", "definition", StatementId.Create(Sha("statement:one")))),
            StatementId.Create(Sha("statement:" + repoPath)),
            WitnessId.Create(Sha("witness:" + repoPath)),
            FrozenNodeId.Create(frozenNodeId),
            ImmutableArray.Create(
                FrozenNodeId.Create(prerequisiteB),
                FrozenNodeId.Create(prerequisiteA)),
            ImmutableArray.Create("propext", "Classical.choice"),
            new FrozenModuleAttestation(
                RepoPath.CreateKnown(repoPath),
                "git-sha1:" + new string('a', 40)));

        var model = TruthExportProjection.Project(
            ImmutableArray.Create(material),
            Commit,
            Tree,
            LeanReportDigest);

        Assert.Equal(Commit, model.SourceCommit);
        Assert.Equal(Tree, model.SourceTree);
        Assert.Equal(LeanReportDigest, model.LeanReportDigest);
        var node = Assert.Single(model.Nodes);
        Assert.Equal(repoPath, node.RepoPath);
        Assert.Equal(frozenNodeId, node.FrozenNodeId);
        Assert.Equal(new[] { "Classical.choice", "propext" }, node.NodeAxiomClosure);
        Assert.Equal(new[] { prerequisiteA, prerequisiteB }, node.PrerequisiteFrozenNodeIds);
        Assert.Equal(new[] { "nk-one", "nk-two" },
            node.Declarations.Select(static declaration => declaration.DeclarationNameKey));
        Assert.Equal("definition", node.Declarations[0].Kind);
        Assert.Equal(Sha("statement:one"), node.Declarations[0].StatementId);
        Assert.Equal("theorem", node.Declarations[1].Kind);
        Assert.Equal(Sha("statement:two"), node.Declarations[1].StatementId);
    }

    private static string Sha(string text) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(text)));
}

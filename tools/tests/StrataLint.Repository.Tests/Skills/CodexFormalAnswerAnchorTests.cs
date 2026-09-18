using static StrataLint.TestSupport.FormalAnswerSkillContract;

namespace StrataLint.Repository.Tests;

public sealed class CodexFormalAnswerAnchorTests
{
    [Fact]
    public void CodexFormalAnswerAnchorsResolveToTrackedTheorems()
    {
        var skill = Parse(File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md")));
        var leanSources = GitIndexRepositoryFiles
            .EnumerateDeclared(TestRepositoryLayout.FindRoot(), "D5")
            .Select(static entry => (entry.RelativePath, Text: File.ReadAllText(entry.FullPath)))
            .ToDictionary(
                static entry => entry.RelativePath,
                static entry => entry.Text,
                StringComparer.Ordinal);
        var methodAnchors = AnchorEntries(skill, MethodAnchorsHeading);
        var selfAnchors = AnchorEntries(skill, SelfAnchorsHeading);

        Assert.NotEmpty(methodAnchors);
        Assert.NotEmpty(selfAnchors);
        Assert.Empty(UnresolvedAnchors(methodAnchors, leanSources));
        Assert.Empty(UnresolvedAnchors(selfAnchors, leanSources));
    }

}

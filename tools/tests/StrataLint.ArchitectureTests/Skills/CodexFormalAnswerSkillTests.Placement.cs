using System.Text.RegularExpressions;
using Markdig.Syntax;

namespace StrataLint.ArchitectureTests;

public sealed partial class CodexFormalAnswerSkillTests
{
    private static readonly Regex RejectsDefaultDestinationPattern = new(
        @"\b(?:is|are)\s+(?:not|never)\s+(?:a\s+)?(?:default\s+)?(?:destination|sink)\b",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    [Fact]
    public void AnswerWorkflowAsDefaultMathematicalDestinationIsRejected()
    {
        var document = Parse(
            """
            ## 4. Implement the inferential completion

            Run a `placement-audit` and choose the `canonical-domain` from the
            `mathematical-subject` and `dependency-neighborhood`. Use
            `D5/S3/ConceptDynamics/Answering/` as the default destination.
            """);

        Assert.False(DefinesCanonicalProjectPlacement(document));
    }

    [Fact]
    public void CodexFormalAnswerPlacesSourceByMathematicalOwnership()
    {
        var skill = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md"));

        Assert.True(DefinesCanonicalProjectPlacement(Parse(skill)));
    }

    private static bool DefinesCanonicalProjectPlacement(MarkdownDocument document)
    {
        var section = FindSection(document, InferentialCompletionHeading);
        var codes = section
            .SelectMany(SelfAndDescendants)
            .SelectMany(InlineCodeValuesFromBlock)
            .ToHashSet(StringComparer.Ordinal);
        var prose = string.Join(
            " ",
            section
                .SelectMany(SelfAndDescendants)
                .OfType<ParagraphBlock>()
                .Select(PlainText));

        return codes.Contains("placement-audit")
            && codes.Contains("canonical-domain")
            && codes.Contains("mathematical-subject")
            && codes.Contains("dependency-neighborhood")
            && codes.Contains("D5/S3/ConceptDynamics/Answering/")
            && RejectsDefaultDestinationPattern.IsMatch(prose);
    }
}

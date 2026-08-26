using System.Text;
using System.Text.RegularExpressions;
using Markdig;
using Markdig.Extensions.Tables;
using Markdig.Syntax;
using Markdig.Syntax.Inlines;

namespace StrataLint.ArchitectureTests;

public sealed class CodexFormalAnswerSkillTests
{
    private const string AuthorityHeading = "5. Derive outcomes from owner facts";
    private const string GeneralizationHeading = "Generalization bridge";
    private const string RepositoryConceptSearchHeading = "Repository concept search";
    private const string DurabilityRoutingHeading = "Durability routing";

    private static readonly MarkdownPipeline Pipeline = new MarkdownPipelineBuilder()
        .UsePipeTables()
        .Build();

    private static readonly Regex FirstMatchPattern = new(
        @"\bfirst(?:\s+|-)match(?:ing)?\b",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private static readonly Regex CatchAllPattern = new(
        @"\botherwise\b",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    [Fact]
    public void RulesOutsideAnOrderedListAreRejected()
    {
        var document = Parse(
            """
            ### 5. Derive outcomes from owner facts

            Apply the first matching rule:

            - alpha
            - beta otherwise

            ## Acceptance

            alpha
            """);

        Assert.False(DefinesSingleStructurallyTotalAuthority(document));
    }

    [Fact]
    public void OrderedListWithoutTerminalCatchAllIsRejected()
    {
        var document = Parse(
            """
            ### 5. Derive outcomes from owner facts

            Apply the first matching rule:

            1. alpha
            2. beta

            ## Acceptance

            alpha
            """);

        Assert.False(DefinesSingleStructurallyTotalAuthority(document));
    }

    [Fact]
    public void ParallelAcceptanceTableIsRejected()
    {
        var document = Parse(
            """
            ### 5. Derive outcomes from owner facts

            Apply the first matching rule:

            1. alpha
            2. beta otherwise

            ## Acceptance

            | Check |
            | --- |
            | alpha |
            """);

        Assert.False(DefinesSingleStructurallyTotalAuthority(document));
    }

    [Fact]
    public void OrderedFirstMatchWithTerminalCatchAllAndNoParallelTableIsAccepted()
    {
        var document = Parse(
            """
            ### 5. Derive outcomes from owner facts

            Apply the first matching rule:

            1. alpha
            2. beta otherwise

            ## Acceptance

            alpha
            """);

        Assert.True(DefinesSingleStructurallyTotalAuthority(document));
    }

    [Fact]
    public void CodexFormalAnswerOutcomeAuthorityIsSingleAndStructurallyTotal()
    {
        Assert.True(
            File.Exists(Path.Combine(
                RepositoryLayout.FindRoot(),
                "skills",
                "codex-formal-answer",
                "SKILL.md")),
            "Required skill file is missing: skills/codex-formal-answer/SKILL.md");
        Assert.True(DefinesSingleStructurallyTotalAuthority(Parse(File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md")))));
    }

    [Fact]
    public void GeneralizationWithoutConcreteSpecializationIsRejected()
    {
        var document = Parse(
            """
            ## Generalization bridge

            1. Record the concrete proposition `P`.
            2. Record the generalized theorem `G`.
            """);

        Assert.False(DefinesCompleteGeneralizationBridge(document));
    }

    [Fact]
    public void CodexFormalAnswerGeneralizationReturnsToTheConcreteProposition()
    {
        var skill = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md"));

        Assert.True(DefinesCompleteGeneralizationBridge(Parse(skill)));
    }

    [Fact]
    public void FormalLibrarySearchWithoutRepositoryConceptDiscoveryIsRejected()
    {
        var document = Parse(
            """
            ## Repository concept search

            1. `F`: Search `D5/` and mathlib for exact declarations.
            2. `M`: Construct `P`, `G`, and `S`.
            """);

        Assert.False(DefinesCompleteRepositoryConceptSearch(document));
    }

    [Fact]
    public void CodexFormalAnswerSearchesRepositoryTheoryBeforeDeclaringAmbiguity()
    {
        var skill = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md"));

        Assert.True(DefinesCompleteRepositoryConceptSearch(Parse(skill)));
    }

    [Fact]
    public void DurabilityRoutingWithoutReuseAndThinBranchesIsRejected()
    {
        var document = Parse(
            """
            ## Durability routing

            1. `deposit-new`: Send every compiling declaration to `codex-formalize`.
            2. `open-deposit`: Report a blocked deposit as `open`.
            """);

        Assert.False(DefinesCompleteDurabilityRouting(document));
    }

    [Fact]
    public void CodexFormalAnswerPersistsOnlySubstantiveNewReusableTheoremsThroughOwner()
    {
        var skill = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md"));

        Assert.True(DefinesCompleteDurabilityRouting(Parse(skill)));
    }

    private static bool DefinesSingleStructurallyTotalAuthority(MarkdownDocument document)
    {
        var authoritySection = FindSection(document, AuthorityHeading);
        var orderedAuthority = FindOrderedFirstMatchList(authoritySection);
        var terminalItemIsCatchAll = orderedAuthority is null
            || IsCatchAll(orderedAuthority.OfType<ListItemBlock>().LastOrDefault());
        var acceptanceAndDecisionSectionsHaveNoTables = document
            .OfType<HeadingBlock>()
            .Where(IsAcceptanceOrDecisionHeading)
            .SelectMany(heading => SectionBlocks(document, heading))
            .SelectMany(SelfAndDescendants)
            .All(block => block is not Table);

        return orderedAuthority is not null
            && terminalItemIsCatchAll
            && acceptanceAndDecisionSectionsHaveNoTables;
    }

    private static bool DefinesCompleteGeneralizationBridge(MarkdownDocument document)
    {
        var headings = document
            .OfType<HeadingBlock>()
            .Where(heading => PlainText(heading).Equals(
                GeneralizationHeading,
                StringComparison.Ordinal))
            .ToArray();
        if (headings.Length != 1)
        {
            return false;
        }

        var orderedLists = SectionBlocks(document, headings[0])
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => list.IsOrdered)
            .ToArray();
        if (orderedLists.Length != 1)
        {
            return false;
        }

        var items = orderedLists[0].OfType<ListItemBlock>().ToArray();
        if (items.Length != 3)
        {
            return false;
        }

        var concreteCodes = InlineCodeValues(items[0]).ToHashSet(StringComparer.Ordinal);
        var generalCodes = InlineCodeValues(items[1]).ToHashSet(StringComparer.Ordinal);
        var specializationCodes = InlineCodeValues(items[2]).ToHashSet(StringComparer.Ordinal);

        return concreteCodes.Contains("P")
            && generalCodes.Contains("G")
            && specializationCodes.Contains("S")
            && specializationCodes.Contains("G")
            && specializationCodes.Contains("P");
    }

    private static bool DefinesCompleteRepositoryConceptSearch(MarkdownDocument document)
    {
        var headings = document
            .OfType<HeadingBlock>()
            .Where(heading => PlainText(heading).Equals(
                RepositoryConceptSearchHeading,
                StringComparison.Ordinal))
            .ToArray();
        if (headings.Length != 1)
        {
            return false;
        }

        var orderedLists = SectionBlocks(document, headings[0])
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => list.IsOrdered)
            .ToArray();
        if (orderedLists.Length != 1)
        {
            return false;
        }

        var items = orderedLists[0].OfType<ListItemBlock>().ToArray();
        if (items.Length != 3)
        {
            return false;
        }

        var discoveryCodes = InlineCodeValues(items[0]).ToHashSet(StringComparer.Ordinal);
        var formalCodes = InlineCodeValues(items[1]).ToHashSet(StringComparer.Ordinal);
        var modelingCodes = InlineCodeValues(items[2]).ToHashSet(StringComparer.Ordinal);

        var requiredDiscoverySurfaces = new[]
        {
            "C",
            "Meta/FILEMAP.toml",
            "D5/",
            "Blueprint/",
            "Library/",
            "Problems/",
            "docs/develop/theory/",
            "Evidence/",
            "Chronicle/",
            "Meta/Digestion/",
        };
        var requiredFormalSurfaces = new[]
        {
            "F",
            "D5/",
            "Blueprint/",
            "Golden/Frozen/accepted/",
            "Meta/Digestion/",
        };

        return requiredDiscoverySurfaces.All(discoveryCodes.Contains)
            && requiredFormalSurfaces.All(formalCodes.Contains)
            && modelingCodes.Contains("M")
            && modelingCodes.Contains("P")
            && modelingCodes.Contains("G")
            && modelingCodes.Contains("S");
    }

    private static bool DefinesCompleteDurabilityRouting(MarkdownDocument document)
    {
        var headings = document
            .OfType<HeadingBlock>()
            .Where(heading => PlainText(heading).Equals(
                DurabilityRoutingHeading,
                StringComparison.Ordinal))
            .ToArray();
        if (headings.Length != 1)
        {
            return false;
        }

        var orderedLists = SectionBlocks(document, headings[0])
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => list.IsOrdered)
            .ToArray();
        if (orderedLists.Length != 1)
        {
            return false;
        }

        var items = orderedLists[0].OfType<ListItemBlock>().ToArray();
        if (items.Length != 4)
        {
            return false;
        }

        var reuseCodes = InlineCodeValues(items[0]).ToHashSet(StringComparer.Ordinal);
        var thinCodes = InlineCodeValues(items[1]).ToHashSet(StringComparer.Ordinal);
        var depositCodes = InlineCodeValues(items[2]).ToHashSet(StringComparer.Ordinal);
        var blockedCodes = InlineCodeValues(items[3]).ToHashSet(StringComparer.Ordinal);

        return reuseCodes.Contains("reuse-existing")
            && reuseCodes.Contains("active-frozen")
            && thinCodes.Contains("discard-thin")
            && thinCodes.Contains("run-local")
            && depositCodes.Contains("deposit-new")
            && depositCodes.Contains("codex-formalize")
            && blockedCodes.Contains("open-deposit")
            && blockedCodes.Contains("open");
    }

    private static ListBlock? FindOrderedFirstMatchList(IReadOnlyList<Block> section)
    {
        var orderedLists = section
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => list.IsOrdered)
            .ToArray();

        if (orderedLists.Length != 1)
        {
            return null;
        }

        var orderedList = orderedLists[0];
        var isIntroducedAsFirstMatch = section
            .SelectMany(SelfAndDescendants)
            .OfType<ParagraphBlock>()
            .Where(paragraph => paragraph.Span.End < orderedList.Span.Start)
            .Any(paragraph => FirstMatchPattern.IsMatch(PlainText(paragraph)));

        return isIntroducedAsFirstMatch ? orderedList : null;
    }

    private static bool IsCatchAll(ListItemBlock? item) =>
        item is not null
        && CatchAllPattern.IsMatch(string.Join(
            " ",
            item.SelectMany(SelfAndDescendants).OfType<LeafBlock>().Select(PlainText)));

    private static IReadOnlyList<Block> FindSection(
        MarkdownDocument document,
        string headingText)
    {
        var headings = document
            .OfType<HeadingBlock>()
            .Where(heading => PlainText(heading).Equals(headingText, StringComparison.Ordinal))
            .ToArray();

        return headings.Length == 1 ? SectionBlocks(document, headings[0]) : [];
    }

    private static IReadOnlyList<Block> SectionBlocks(
        MarkdownDocument document,
        HeadingBlock heading)
    {
        var section = new List<Block>();
        var inside = false;

        foreach (var block in document)
        {
            if (ReferenceEquals(block, heading))
            {
                inside = true;
                continue;
            }

            if (!inside)
            {
                continue;
            }

            if (block is HeadingBlock nextHeading && nextHeading.Level <= heading.Level)
            {
                break;
            }

            section.Add(block);
        }

        return section;
    }

    private static IEnumerable<Block> SelfAndDescendants(Block block)
    {
        yield return block;

        if (block is not ContainerBlock container)
        {
            yield break;
        }

        foreach (var child in container)
        {
            foreach (var descendant in SelfAndDescendants(child))
            {
                yield return descendant;
            }
        }
    }

    private static IEnumerable<string> InlineCodeValues(Block block)
    {
        foreach (var leaf in SelfAndDescendants(block).OfType<LeafBlock>())
        {
            foreach (var value in InlineCodeValues(leaf.Inline?.FirstChild))
            {
                yield return value;
            }
        }
    }

    private static IEnumerable<string> InlineCodeValues(Inline? inline)
    {
        for (var current = inline; current is not null; current = current.NextSibling)
        {
            if (current is CodeInline code)
            {
                yield return code.Content;
            }

            if (current is ContainerInline container)
            {
                foreach (var value in InlineCodeValues(container.FirstChild))
                {
                    yield return value;
                }
            }
        }
    }

    private static string PlainText(LeafBlock block)
    {
        var text = new StringBuilder();
        AppendInlineText(block.Inline?.FirstChild, text);
        return text.ToString();
    }

    private static void AppendInlineText(Inline? inline, StringBuilder text)
    {
        for (var current = inline; current is not null; current = current.NextSibling)
        {
            switch (current)
            {
                case LiteralInline literal:
                    text.Append(literal.Content);
                    break;
                case CodeInline code:
                    text.Append(code.Content);
                    break;
                case ContainerInline container:
                    AppendInlineText(container.FirstChild, text);
                    break;
            }
        }
    }

    private static bool IsAcceptanceOrDecisionHeading(HeadingBlock heading)
    {
        var text = PlainText(heading);
        return StartsWithWord(text, "Acceptance") || StartsWithWord(text, "Decision");
    }

    private static bool StartsWithWord(string text, string word) =>
        text.Equals(word, StringComparison.OrdinalIgnoreCase)
        || text.StartsWith(word + " ", StringComparison.OrdinalIgnoreCase);

    private static MarkdownDocument Parse(string markdown) => Markdown.Parse(markdown, Pipeline);
}

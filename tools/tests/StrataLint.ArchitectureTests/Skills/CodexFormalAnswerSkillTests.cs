using System.Text;
using System.Text.RegularExpressions;
using Markdig;
using Markdig.Extensions.Tables;
using Markdig.Syntax;
using Markdig.Syntax.Inlines;

namespace StrataLint.ArchitectureTests;

public sealed class CodexFormalAnswerSkillTests
{
    private const string AuthorityHeading = "5. Settle outcomes and freeze the answer register";
    private const string GeneralizationHeading = "3. Fix the exact statement echo";
    private const string RepositoryConceptSearchHeading = "2. Search and model";
    private const string InferentialCompletionHeading = "4. Implement the inferential completion";
    private const string ProjectPersistenceHeading = "6. Persist project source and account for the worktree";

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
            ### 5. Settle outcomes and freeze the answer register

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
            ### 5. Settle outcomes and freeze the answer register

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
            ### 5. Settle outcomes and freeze the answer register

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
            ### 5. Settle outcomes and freeze the answer register

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
            ## 3. Fix the exact statement echo

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
            ## 2. Search and model

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
    public void SearchWithoutInferentialCompletionIsRejected()
    {
        var document = Parse(
            """
            ## 2. Search and model

            1. `C`: Search repository concepts.
            2. `F`: Search Lean declarations.
            3. `M`: Render the hits as an answer.

            ## 6. Persist project source and account for the worktree

            1. `reuse-complete`: cite a hit.
            2. `discard-thin`: discard `run-local` wrappers.
            3. `persist-synthesis`: retain `tracked-lean` after `make lean`.
            4. `open-compile`: preserve an `open` compiler failure.
            """);

        Assert.False(DefinesInferentialCompletionAndProjectPersistence(document));
    }

    [Fact]
    public void TruthDagGatedPersistenceIsRejected()
    {
        var document = Parse(
            """
            ## 3. Fix the exact statement echo

            1. `premise-map`: identify premises.
            2. `G`: derive a reusable theorem.
            3. `S`: apply `G` to exact `P`.

            ## 6. Persist project source and account for the worktree

            1. `reuse-complete`: require `active-frozen` evidence.
            2. `discard-thin`: discard `run-local` wrappers.
            3. `persist-synthesis`: invoke `codex-formalize` and `deposit-new`.
            4. `open-compile`: preserve an `open` compiler failure.
            """);

        Assert.False(DefinesInferentialCompletionAndProjectPersistence(document));
    }

    [Fact]
    public void CodexFormalAnswerCompletesInferenceAndPersistsCompiledProjectSource()
    {
        var skill = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md"));

        Assert.True(DefinesInferentialCompletionAndProjectPersistence(Parse(skill)));
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

        var concreteCodes = InlineCodeValuesFromBlock(items[0]).ToHashSet(StringComparer.Ordinal);
        var generalCodes = InlineCodeValuesFromBlock(items[1]).ToHashSet(StringComparer.Ordinal);
        var specializationCodes = InlineCodeValuesFromBlock(items[2]).ToHashSet(StringComparer.Ordinal);

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

        var discoveryCodes = InlineCodeValuesFromBlock(items[0]).ToHashSet(StringComparer.Ordinal);
        var formalCodes = InlineCodeValuesFromBlock(items[1]).ToHashSet(StringComparer.Ordinal);
        var modelingCodes = InlineCodeValuesFromBlock(items[2]).ToHashSet(StringComparer.Ordinal);

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
            ".lake/packages/mathlib/Mathlib/",
        };

        return requiredDiscoverySurfaces.All(discoveryCodes.Contains)
            && requiredFormalSurfaces.All(formalCodes.Contains)
            && modelingCodes.Contains("M")
            && modelingCodes.Contains("P")
            && modelingCodes.Contains("G")
            && modelingCodes.Contains("S");
    }

    private static bool DefinesInferentialCompletionAndProjectPersistence(
        MarkdownDocument document)
    {
        var completionHeadings = document
            .OfType<HeadingBlock>()
            .Where(heading => PlainText(heading).Equals(
                InferentialCompletionHeading,
                StringComparison.Ordinal))
            .ToArray();
        var persistenceHeadings = document
            .OfType<HeadingBlock>()
            .Where(heading => PlainText(heading).Equals(
                ProjectPersistenceHeading,
                StringComparison.Ordinal))
            .ToArray();
        if (completionHeadings.Length != 1 || persistenceHeadings.Length != 1)
        {
            return false;
        }

        var completionLists = SectionBlocks(document, completionHeadings[0])
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => list.IsOrdered)
            .ToArray();
        var persistenceLists = SectionBlocks(document, persistenceHeadings[0])
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => list.IsOrdered)
            .ToArray();
        if (completionLists.Length != 1 || persistenceLists.Length != 1)
        {
            return false;
        }

        var completionItems = completionLists[0].OfType<ListItemBlock>().ToArray();
        var persistenceItems = persistenceLists[0].OfType<ListItemBlock>().ToArray();
        if (completionItems.Length != 3 || persistenceItems.Length != 4)
        {
            return false;
        }

        var premiseCodes = InlineCodeValuesFromBlock(completionItems[0]).ToHashSet(StringComparer.Ordinal);
        var generalCodes = InlineCodeValuesFromBlock(completionItems[1]).ToHashSet(StringComparer.Ordinal);
        var specializationCodes = InlineCodeValuesFromBlock(completionItems[2]).ToHashSet(StringComparer.Ordinal);
        var reuseCodes = InlineCodeValuesFromBlock(persistenceItems[0]).ToHashSet(StringComparer.Ordinal);
        var thinCodes = InlineCodeValuesFromBlock(persistenceItems[1]).ToHashSet(StringComparer.Ordinal);
        var persistenceCodes = InlineCodeValuesFromBlock(persistenceItems[2]).ToHashSet(StringComparer.Ordinal);
        var blockedCodes = InlineCodeValuesFromBlock(persistenceItems[3]).ToHashSet(StringComparer.Ordinal);
        var allCodes = document
            .SelectMany(SelfAndDescendants)
            .SelectMany(InlineCodeValuesFromBlock)
            .ToHashSet(StringComparer.Ordinal);
        var forbiddenTruthDagDependencies = new[]
        {
            "active-frozen",
            "Golden/Frozen/accepted/",
            "codex-formalize",
            "deposit-new",
            "open-deposit",
        };

        return premiseCodes.Contains("premise-map")
            && generalCodes.Contains("G")
            && specializationCodes.Contains("S")
            && specializationCodes.Contains("G")
            && specializationCodes.Contains("P")
            && reuseCodes.Contains("reuse-complete")
            && reuseCodes.Contains("project-source")
            && thinCodes.Contains("discard-thin")
            && thinCodes.Contains("run-local")
            && persistenceCodes.Contains("persist-synthesis")
            && persistenceCodes.Contains("tracked-lean")
            && persistenceCodes.Contains("Describe")
            && persistenceCodes.Contains("make lean")
            && blockedCodes.Contains("open-compile")
            && blockedCodes.Contains("open")
            && forbiddenTruthDagDependencies.All(code => !allCodes.Contains(code));
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

    private static IEnumerable<string> InlineCodeValuesFromBlock(Block block)
    {
        foreach (var leaf in SelfAndDescendants(block).OfType<LeafBlock>())
        {
            foreach (var value in InlineCodeValuesFromInline(leaf.Inline?.FirstChild))
            {
                yield return value;
            }
        }
    }

    private static IEnumerable<string> InlineCodeValuesFromInline(Inline? inline)
    {
        for (var current = inline; current is not null; current = current.NextSibling)
        {
            if (current is CodeInline code)
            {
                yield return code.Content;
            }

            if (current is ContainerInline container)
            {
                foreach (var value in InlineCodeValuesFromInline(container.FirstChild))
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

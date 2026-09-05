using System.Text.Json;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeMigrationTests
{

    private static IEnumerable<DocumentBlock.Describe> EnumerateDescribe(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            switch (block)
            {
                case DocumentBlock.Section section:
                    foreach (var nested in EnumerateDescribe(section.Content))
                    {
                        yield return nested;
                    }
                    break;
                case DocumentBlock.Describe describe:
                    yield return describe;
                    foreach (var nested in EnumerateDescribe(describe.Content))
                    {
                        yield return nested;
                    }
                    break;
            }
        }
    }

    [Fact]
    public void LegacyNarrativeNodeTypesAreAbsentAfterTheSingleStepMigration()
    {
        var nestedNames = typeof(DocumentBlock).GetNestedTypes()
            .Select(static type => type.Name)
            .ToHashSet(StringComparer.Ordinal);

        Assert.DoesNotContain("Proposition", nestedNames);
        Assert.DoesNotContain("Theorem", nestedNames);
        Assert.DoesNotContain("ComputedValue", nestedNames);
        Assert.DoesNotContain("RenderedStatement", nestedNames);
    }

    private static IEnumerable<DocumentBlock> EnumerateBlocks(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (nested is null)
            {
                continue;
            }

            foreach (var descendant in EnumerateBlocks(nested))
            {
                yield return descendant;
            }
        }
    }

}

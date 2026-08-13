using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

internal static class DocumentFactAssertions
{
    internal static void Declaration(
        DocumentBlock.Describe describe,
        LeanDeclarationKind expectedKind)
    {
        var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
        var handle = DeclarationHandle.Create(statement.Value.Value);
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [handle.Reference!.Path.Value] = new(
                [],
                [new LeanDeclaration(
                    statement.Value.Value.Replace('/', '.'),
                    expectedKind switch
                    {
                        LeanDeclarationKind.Definition => "def",
                        LeanDeclarationKind.Theorem => "theorem",
                        _ => throw new InvalidOperationException(
                            $"Unsupported fixture declaration kind {expectedKind}."),
                    },
                    $"statement-v1(source={statement.Value.Value})",
                    ImmutableArray.Create("propext", "Classical.choice", "Quot.sound"))]),
        });
        var resolved = DeclarationCatalog.Create(report).Resolve(handle);

        Assert.Equal(expectedKind, resolved.FormalKind);
        Assert.True(resolved.IsSorryFree);
    }

    internal static void RepoDerived(DocumentBlock.Describe describe) =>
        Assert.IsType<AssessedProvenance.RepoDerived>(describe.AssessedProvenance);

    internal static void LiteratureAttested(
        DocumentBlock.Describe describe,
        string expectedReference)
    {
        var provenance = Assert.IsType<AssessedProvenance.LiteratureAttested>(
            describe.AssessedProvenance);
        Assert.Equal(expectedReference, provenance.NoteRef.Value);
    }

}

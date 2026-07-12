using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class LeanReferenceTests
{
    private const string Gid = "D5/S1/Phase/Basic.goldenPhase_injective";
    private const string ModulePath = "D5/S1/Phase/Basic.lean";

    [Fact]
    public void MissingDeclarationFailsClosed()
    {
        var reference = Reference();
        var report = Report(
            new LeanDeclaration("another_declaration", "theorem", "statement-v1(other)", []));

        var exception = Assert.Throws<InvalidOperationException>(
            () => LeanReferenceResolver.Resolve(reference, report));

        Assert.Contains(Gid, exception.Message, StringComparison.Ordinal);
        Assert.Contains("does not contain", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ExpectedKindMismatchFailsClosed()
    {
        var reference = Reference();
        var report = Report(Declaration(kind: "def"));

        var exception = Assert.Throws<InvalidOperationException>(
            () => LeanReferenceResolver.Resolve(reference, report));

        Assert.Contains("expected theorem", exception.Message, StringComparison.Ordinal);
        Assert.Contains("found def", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RequiredNoSorryRejectsSorryAxiomClosure()
    {
        var reference = Reference();
        var report = Report(Declaration(axioms: ["sorryAx"]));

        var exception = Assert.Throws<InvalidOperationException>(
            () => LeanReferenceResolver.Resolve(reference, report));

        Assert.Contains("sorryAx", exception.Message, StringComparison.Ordinal);
        Assert.Contains("requires a sorry-free", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AxiomClosureProducesHonestBadges()
    {
        var strict = LeanReferenceResolver.Resolve(
            Reference(),
            Report(Declaration(axioms: ["propext", "Classical.choice", "Quot.sound"])));
        var sorry = LeanReferenceResolver.Resolve(
            LeanDeclarationRef.Create(
                Gid,
                expectedKind: LeanDeclarationKind.Theorem,
                requireNoSorry: false),
            Report(Declaration(axioms: ["sorryAx"])));

        Assert.Equal("✓ std3", strict.AxiomBadge);
        Assert.Equal("⚠ sorryAx", sorry.AxiomBadge);
    }

    [Fact]
    public void RenderedStatementCopiesTypeRepresentationBytesFromCompiledReport()
    {
        const string typeRepresentation =
            "statement-v1(uparams=[],type=ep(bd,ec(ns(n0,3:Nat),[]),eb(0)))";
        var reference = Reference();
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Phase/Basic", "Rendered statement fixture."),
            Heading.Create("Compiled statement fixture"),
            BlockSequence.Create([new DocumentBlock.RenderedStatement(reference)]));

        var markdown = CanonicalMarkdownWriter.Write(
            document,
            Report(Declaration(typeRepresentation: typeRepresentation)));
        var text = Encoding.UTF8.GetString(markdown.AsSpan());
        var prefix = "```text\n";
        var start = text.IndexOf(prefix, StringComparison.Ordinal) + prefix.Length;
        var end = text.IndexOf("\n```", start, StringComparison.Ordinal);

        Assert.True(start >= prefix.Length);
        Assert.True(end >= start);
        Assert.Equal(
            Encoding.UTF8.GetBytes(typeRepresentation),
            Encoding.UTF8.GetBytes(text[start..end]));
        Assert.Contains($"Compiled Lean statement: `{Gid}` `✓ std3`", text, StringComparison.Ordinal);
    }

    private static LeanDeclarationRef Reference() =>
        LeanDeclarationRef.Create(
            Gid,
            expectedKind: LeanDeclarationKind.Theorem,
            requireNoSorry: true);

    private static LeanDeclaration Declaration(
        string kind = "theorem",
        string typeRepresentation = "statement-v1(fixture)",
        string[]? axioms = null) =>
        new(
            "D5.S1.Phase.goldenPhase_injective",
            kind,
            typeRepresentation,
            axioms is null ? [] : [.. axioms]);

    private static LeanAxiomReport Report(params LeanDeclaration[] declarations) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [ModulePath] = new LeanFileReport([], declarations.ToImmutableArray()),
        });
}

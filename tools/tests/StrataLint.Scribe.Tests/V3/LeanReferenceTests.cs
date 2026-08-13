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
    public void AStandardAxiomClosureBadgesAsStd3()
    {
        var strict = LeanReferenceResolver.Resolve(
            Reference(),
            Report(Declaration(axioms: ["propext", "Classical.choice", "Quot.sound"])));

        Assert.Equal("✓ std3", strict.AxiomBadge);
    }

    [Fact]
    public void ASorryBearingDeclarationIsRefused()
    {
        // This used to resolve and carry a "⚠ sorryAx" badge, reachable only by passing
        // requireNoSorry: false. That opt-out is gone: the sole production caller never passed it,
        // so the check never ran here, while DeclarationCatalog.Resolve — the path every
        // report-derived Describe node takes — has always refused a sorryAx closure outright.
        // The two paths now agree, and a document cannot cite an incomplete proof either way.
        Assert.Throws<InvalidOperationException>(() => LeanReferenceResolver.Resolve(
            LeanDeclarationRef.Create(Gid),
            Report(Declaration(axioms: ["sorryAx"]))));
    }

    [Fact]
    public void DescribeLeanStatementResolvesAgainstTheCompiledReport()
    {
        const string typeRepresentation =
            "statement-v1(uparams=[],type=ep(bd,ec(ns(n0,3:Nat),[]),eb(0)))";
        var reference = Reference();
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Phase/Basic", "Rendered statement fixture."),
            Heading.Create("Compiled statement fixture"),
            BlockSequence.Create(
            [
                Describe.Lean(
                    DescribeId.Create("compiled-theorem"),
                    DeclarationHandle.Create(reference.Value),
                    Heading.Create("Compiled theorem"),
                    StatementSource.FromAuthor(new Formula.Layout(
                        FormulaLayoutMode.Inline,
                        new Formula.Relation(
                            new Formula.Symbol(FormulaIdentifier.Create("x")),
                            FormulaRelationOperator.Equal,
                            new Formula.Symbol(FormulaIdentifier.Create("x"))))),
                    AssessedProvenance.FromRepo(),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Resolved statement.")),
                    ]),
                    DescribeRole.Theorem
                ),
            ]));

        var markdown = CanonicalMarkdownWriter.Write(
            document,
            DeclarationCatalog.Create(Report(Declaration(typeRepresentation: typeRepresentation))));
        var text = Encoding.UTF8.GetString(markdown.AsSpan());
        Assert.Contains("$x = x$", text, StringComparison.Ordinal);
        Assert.Contains(
            $"*Proof.* Machine-checked in Lean as `{Gid}` (`✓ std3`). ∎",
            text,
            StringComparison.Ordinal);
        Assert.DoesNotContain(typeRepresentation, text, StringComparison.Ordinal);
    }

    private static LeanDeclarationRef Reference() => LeanDeclarationRef.Create(Gid);

    private static LeanDeclaration Declaration(
        string kind = "theorem",
        string typeRepresentation = "statement-v1(fixture)",
        string[]? axioms = null) =>
        new(
            Gid.Replace('/', '.'),
            kind,
            typeRepresentation,
            axioms is null ? [] : [.. axioms]);

    private static LeanAxiomReport Report(params LeanDeclaration[] declarations) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [ModulePath] = new LeanFileReport([], declarations.ToImmutableArray()),
        });
}

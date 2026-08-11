using System.Collections.Immutable;
using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class CanonicalMarkdownWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static ImmutableArray<byte> Write(
        ScribeDocument document,
        LeanAxiomReport? leanReport = null,
        IReadOnlyDictionary<string, LiteratureCitation>? citations = null,
        DocumentGraph? graph = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        if (leanReport is not null && document.HasReportDerivedDeclarations)
        {
            document = document.ResolveDeclarations(DeclarationCatalog.Create(leanReport));
        }
        var builder = new StringBuilder();
        builder.Append("# ").Append(document.Title.Value).Append("\n\n");
        builder.Append("## Abstract\n\n")
            .Append(document.Header.Digest.Value)
            .Append("\n\n");
        var describeNumber = 0;
        var referencedDescribeIds = graph?.ReferencedDescribeIds(document)
            ?? ReferencedDescribeIds(document, DocumentGraphAssembler.Extract(document));
        WriteBlocks(
            builder,
            document.Content,
            2,
            $"document '{document.Header.Gid.Value}'",
            leanReport,
            citations,
            referencedDescribeIds,
            ref describeNumber);
        WriteReferences(
            builder,
            document,
            graph is null
                ? document.Edges.IsEmpty ? [] : DocumentGraphAssembler.Extract(document)
                : graph.For(document));
        builder.Append('\n');
        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    private static void WriteBlocks(
        StringBuilder builder,
        BlockSequence content,
        int headingLevel,
        string source,
        LeanAxiomReport? leanReport,
        IReadOnlyDictionary<string, LiteratureCitation>? citations,
        IReadOnlySet<string> referencedDescribeIds,
        ref int describeNumber)
    {
        for (var index = 0; index < content.Items.Length; index++)
        {
            if (index > 0)
            {
                builder.Append("\n\n");
            }

            WriteBlock(
                builder,
                content.Items[index],
                headingLevel,
                $"{source}, block {index + 1}",
                leanReport,
                citations,
                referencedDescribeIds,
                ref describeNumber);
        }
    }

    private static void WriteBlock(
        StringBuilder builder,
        DocumentBlock block,
        int headingLevel,
        string source,
        LeanAxiomReport? leanReport,
        IReadOnlyDictionary<string, LiteratureCitation>? citations,
        IReadOnlySet<string> referencedDescribeIds,
        ref int describeNumber)
    {
        switch (block)
        {
            case DocumentBlock.Paragraph paragraph:
                WriteParagraph(builder, paragraph.Content, $"{source}, paragraph");
                break;
            case DocumentBlock.DisplayFormula display:
                builder.Append("$$\n")
                    .Append(LatexWriter.Write(display.Value, $"{source}, display formula"))
                    .Append("\n$$");
                break;
            case DocumentBlock.Section section:
                WriteHeading(builder, headingLevel, section.Title.Value);
                builder.Append("\n\n");
                WriteBlocks(
                    builder,
                    section.Content,
                    headingLevel + 1,
                    $"{source}, section '{section.Title.Value}'",
                    leanReport,
                    citations,
                    referencedDescribeIds,
                    ref describeNumber);
                break;
            case DocumentBlock.Describe describe:
                WriteDescribe(
                    builder,
                    describe,
                    headingLevel,
                    source,
                    leanReport,
                    citations,
                    referencedDescribeIds,
                    ref describeNumber);
                break;
            default:
                throw new UnreachableException("Unknown document block.");
        }
    }

    private static void WriteParagraph(
        StringBuilder builder,
        InlineSequence content,
        string source)
    {
        foreach (var inline in content.Items)
        {
            switch (inline)
            {
                case Inline.Text text:
                    builder.Append(text.Run.Value);
                    break;
                case Inline.InlineFormula formula:
                    builder.Append('$')
                        .Append(LatexWriter.Write(formula.Value, $"{source}, inline formula"))
                        .Append('$');
                    break;
                case Inline.GidReference reference:
                    builder.Append('`').Append(reference.Reference.Value).Append('`');
                    break;
                default:
                    throw new UnreachableException("Unknown inline node.");
            }
        }
    }

    private static void WriteDescribe(
        StringBuilder builder,
        DocumentBlock.Describe describe,
        int headingLevel,
        string source,
        LeanAxiomReport? leanReport,
        IReadOnlyDictionary<string, LiteratureCitation>? citations,
        IReadOnlySet<string> referencedDescribeIds,
        ref int describeNumber)
    {
        describeNumber++;
        if (referencedDescribeIds.Contains(describe.Id.Value))
        {
            builder.Append("<a id=\"describe-")
                .Append(describe.Id.Value)
                .Append("\"></a>\n\n");
        }
        builder.Append("**")
            .Append(DescribeVocabulary.HeadingName(describe.Kind))
            .Append(" 1.")
            .Append(describeNumber)
            .Append(" (")
            .Append(describe.Title.Value)
            .Append(").**");
        switch (describe.Statement)
        {
            case DescribeStatement.FormulaAst formula:
                builder.Append("\n\n$$\n")
                    .Append(LatexWriter.Write(
                        formula.Value,
                        $"{source}, describe '{describe.Id.Value}' ('{describe.Title.Value}') statement"))
                    .Append("\n$$");
                break;
            case DescribeStatement.LeanDeclaration lean:
                var verified = Resolve(lean.Value, leanReport);
                if (describe.StatementFormula is { } statementFormula)
                {
                    builder.Append("\n\n")
                        .Append(LatexWriter.WriteStatement(
                            statementFormula,
                            $"{source}, describe '{describe.Id.Value}' ('{describe.Title.Value}') statement"));
                }
                else
                {
                    builder.Append("\n\nLean statement: `")
                        .Append(lean.Value.Value)
                        .Append('`');
                }

                if (IsTheoremClass(describe.Kind))
                {
                    builder.Append("\n\n*Proof.* Machine-checked in Lean as `")
                        .Append(lean.Value.Value)
                        .Append("` (`")
                        .Append(verified.AxiomBadge)
                        .Append("`). ∎");
                }
                else
                {
                    builder.Append("\n\n*Formalization.* `")
                        .Append(lean.Value.Value)
                        .Append("` (`")
                        .Append(verified.AxiomBadge)
                        .Append("`).");
                }
                break;
            default:
                throw new UnreachableException("Unknown Describe statement.");
        }

        if (describe.Provenance.LiteratureReference is { } literature)
        {
            if (citations is null
                || !citations.TryGetValue(literature.BibKey.Value, out var citation))
            {
                throw new InvalidOperationException(
                    $"Academic citation is unavailable for {literature.Value}.");
            }

            builder.Append("\n\n*Citation.* ")
                .Append(citation.Authors)
                .Append(" (")
                .Append(citation.Year)
                .Append("). *")
                .Append(citation.Title)
                .Append("*. DOI: [")
                .Append(citation.Doi.Value)
                .Append("](https://doi.org/")
                .Append(citation.Doi.Value)
                .Append(").");
        }
        else
        {
            builder.Append("\n\n*Source.* ");
            builder.Append(DescribeVocabulary.CanonicalName(describe.Provenance.Kind) switch
            {
                "repo-derived" => "Repository-derived.",
                "suspected-novel" => "Suspected novel.",
                "unassessed" => "Unassessed.",
                var provenance => provenance + ".",
            });
        }

        builder.Append("\n\n*Commentary.*\n\n");
        WriteBlocks(
            builder,
            describe.Content,
            headingLevel + 1,
            $"{source}, describe '{describe.Id.Value}' ('{describe.Title.Value}') commentary",
            leanReport,
            citations,
            referencedDescribeIds,
            ref describeNumber);
    }

    private static IReadOnlySet<string> ReferencedDescribeIds(
        ScribeDocument document,
        IEnumerable<DocumentEdge> edges) =>
        edges
            .OfType<DocumentEdge.NarrativeReference>()
            .Select(static edge => edge.Target)
            .OfType<NarrativeTarget.Describe>()
            .Where(target => string.Equals(
                target.DocumentGid.Value,
                document.Header.Gid.Value,
                StringComparison.Ordinal))
            .Select(static target => target.DescribeId.Value)
            .ToHashSet(StringComparer.Ordinal);

    private static bool IsTheoremClass(DescribeKind kind) =>
        kind is DescribeKind.Theorem or DescribeKind.Proposition or DescribeKind.Lemma;

    private static VerifiedLeanDeclaration Resolve(
        LeanDeclarationRef declaration,
        LeanAxiomReport? leanReport) =>
        LeanReferenceResolver.Resolve(
            declaration,
            leanReport ?? throw new InvalidOperationException(
                $"Lean compiled-artifact report is required for {declaration.Value}."));

    private static void WriteHeading(
        StringBuilder builder,
        int headingLevel,
        string title)
    {
        if (headingLevel is < 2 or > 6)
        {
            throw new InvalidOperationException("Markdown heading depth exceeds level six.");
        }

        builder.Append('#', headingLevel).Append(' ').Append(title);
    }

    private static void WriteReferences(
        StringBuilder builder,
        ScribeDocument source,
        IEnumerable<DocumentEdge> edges)
    {
        var ordered = edges
            .DistinctBy(DocumentGraphAssembler.CanonicalKey, StringComparer.Ordinal)
            .OrderBy(DocumentGraphAssembler.RoleOrder)
            .ThenBy(DocumentGraphAssembler.CanonicalKey, StringComparer.Ordinal)
            .ToArray();
        if (ordered.Length == 0)
        {
            return;
        }

        builder.Append("\n\n## References\n\n");
        for (var index = 0; index < ordered.Length; index++)
        {
            if (index > 0)
            {
                builder.Append('\n');
            }
            switch (ordered[index])
            {
                case DocumentEdge.TruthAnchor truth:
                    builder.Append("- Truth anchor: `").Append(truth.Target.Value).Append('`');
                    break;
                case DocumentEdge.Dependency dependency:
                    WriteDocumentLink(builder, "Dependency", source, dependency.Target);
                    break;
                case DocumentEdge.NarrativeReference { Target: NarrativeTarget.Document document }:
                    WriteDocumentLink(builder, "Narrative reference", source, document.DocumentGid);
                    break;
                case DocumentEdge.NarrativeReference { Target: NarrativeTarget.Describe describe }:
                    WriteDocumentLink(
                        builder,
                        "Narrative reference",
                        source,
                        describe.DocumentGid,
                        describe.DescribeId);
                    break;
                default:
                    throw new UnreachableException("Unknown document edge.");
            }
        }
    }

    private static void WriteDocumentLink(
        StringBuilder builder,
        string role,
        ScribeDocument source,
        GidRef target,
        DescribeId? describe = null)
    {
        var targetPath = GidRef.Create(
            "D5/B/" + target.Value["D5/".Length..]).Path.Value;
        var sourceDirectory = Path.GetDirectoryName(source.Header.MirrorBlueprint.Path.Value)
            ?? throw new InvalidOperationException("Scribe document has no parent directory.");
        var relative = Path.GetRelativePath(sourceDirectory, targetPath).Replace('\\', '/');
        var label = target.Value + (describe is null ? "" : $"#describe/{describe.Value}");
        var anchor = describe is null ? "" : $"#describe-{describe.Value}";
        builder.Append("- ").Append(role).Append(": [")
            .Append(label).Append("](").Append(relative).Append(anchor).Append(')');
    }
}

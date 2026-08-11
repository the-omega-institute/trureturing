using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public enum StatementFormulaProvenance
{
    HandAuthored,
    LeanDerived,
}

public sealed record Heading
{
    private Heading(string value) => Value = value;

    public string Value { get; }

    public static Heading Create(string value) =>
        !string.IsNullOrWhiteSpace(value)
        && string.Equals(value, value.Trim(), StringComparison.Ordinal)
        && value.IndexOfAny(['\r', '\n']) < 0
            ? new Heading(value)
            : throw new ArgumentException("Heading must be one non-empty canonical line.", nameof(value));

    public override string ToString() => Value;
}

public sealed record TextRun
{
    private TextRun(string value) => Value = value;

    public string Value { get; }

    public static TextRun Create(string value) =>
        value is { Length: > 0 }
        && value.IndexOfAny(['\r', '\n', '$']) < 0
        && !value.Contains("\\(", StringComparison.Ordinal)
        && !value.Contains("\\)", StringComparison.Ordinal)
        && !value.Contains("\\[", StringComparison.Ordinal)
        && !value.Contains("\\]", StringComparison.Ordinal)
            ? new TextRun(value)
            : throw new ArgumentException(
                "Text run must be non-empty, single-line, and free of raw LaTeX delimiters.",
                nameof(value));

    public override string ToString() => Value;
}

public abstract record Inline
{
    private Inline() { }

    public sealed record Text(TextRun Run) : Inline;

    public sealed record InlineFormula(Formula Value) : Inline;

    public sealed record GidReference(GidRef Reference) : Inline;
}

public sealed class InlineSequence
{
    private InlineSequence(ImmutableArray<Inline> items) => Items = items;

    public ImmutableArray<Inline> Items { get; }

    public static InlineSequence Create(IEnumerable<Inline> items)
    {
        ArgumentNullException.ThrowIfNull(items);
        var values = items.ToImmutableArray();
        if (values.IsEmpty || values.Any(static value => value is null))
        {
            throw new ArgumentException(
                "Inline sequence must contain at least one non-null node.",
                nameof(items));
        }

        return new InlineSequence(values);
    }
}

public sealed class BlockSequence
{
    private BlockSequence(ImmutableArray<DocumentBlock> items) => Items = items;

    public ImmutableArray<DocumentBlock> Items { get; }

    public static BlockSequence Create(IEnumerable<DocumentBlock> items)
    {
        ArgumentNullException.ThrowIfNull(items);
        var values = items.ToImmutableArray();
        if (values.IsEmpty || values.Any(static value => value is null))
        {
            throw new ArgumentException(
                "Block sequence must contain at least one non-null node.",
                nameof(items));
        }

        return new BlockSequence(values);
    }
}

public abstract record DocumentBlock
{
    private DocumentBlock() { }

    public sealed record Paragraph(InlineSequence Content) : DocumentBlock;

    public sealed record DisplayFormula(Formula Value) : DocumentBlock;

    public sealed record Section(Heading Title, BlockSequence Content) : DocumentBlock;

    public sealed record Describe : DocumentBlock
    {
        private Describe(
            DescribeId id,
            DescribeKind kind,
            Heading title,
            DescribeStatement statement,
            DescribeProvenance provenance,
            BlockSequence content,
            Formula? statementFormula = null,
            DescribeKindSource? kindSource = null)
        {
            Id = id ?? throw new ArgumentNullException(nameof(id));
            Title = title ?? throw new ArgumentNullException(nameof(title));
            Statement = statement ?? throw new ArgumentNullException(nameof(statement));
            Provenance = provenance ?? throw new ArgumentNullException(nameof(provenance));
            Content = content ?? throw new ArgumentNullException(nameof(content));
            StatementFormula = statementFormula;
            FormulaProvenance = statementFormula is not null
                && statement is DescribeStatement.LeanDeclaration lean
                && StatementProjectionFixtureLoader.IsDerivedFrom(statementFormula, lean.Value)
                ? StatementFormulaProvenance.LeanDerived
                : StatementFormulaProvenance.HandAuthored;
            Kind = kind is DescribeKind.Definition
                or DescribeKind.Theorem
                or DescribeKind.Proposition
                or DescribeKind.Lemma
                or DescribeKind.Example
                or DescribeKind.Remark
                    ? kind
                    : throw new ArgumentOutOfRangeException(nameof(kind));
            KindSource = kindSource ?? new DescribeKindSource.Authored(kind);
        }

        public DescribeId Id { get; }

        public DescribeKind Kind { get; }

        internal DescribeKindSource KindSource { get; }

        internal Describe Resolve(DeclarationCatalog catalog)
        {
            ArgumentNullException.ThrowIfNull(catalog);
            var resolvedContent = ResolveBlocks(Content, catalog);
            var resolvedKind = catalog.ResolveKind(this);
            return new Describe(
                Id,
                resolvedKind,
                Title,
                Statement,
                Provenance,
                resolvedContent,
                StatementFormula);
        }

        public Heading Title { get; }

        public DescribeStatement Statement { get; }

        public DescribeProvenance Provenance { get; }

        public BlockSequence Content { get; }

        public Formula? StatementFormula { get; }

        public StatementFormulaProvenance FormulaProvenance { get; }

        public static Describe Theorem(
            DescribeId id,
            Heading title,
            LeanDeclarationRef leanRef,
            Formula formula,
            DescribeProvenance provenance,
            BlockSequence content) =>
            LeanDescribe(id, DescribeKind.Theorem, title, leanRef, provenance, content, formula);

        public static Describe Proposition(
            DescribeId id,
            Heading title,
            LeanDeclarationRef leanRef,
            Formula formula,
            DescribeProvenance provenance,
            BlockSequence content) =>
            LeanDescribe(id, DescribeKind.Proposition, title, leanRef, provenance, content, formula);

        public static Describe Lemma(
            DescribeId id,
            Heading title,
            LeanDeclarationRef leanRef,
            Formula formula,
            DescribeProvenance provenance,
            BlockSequence content) =>
            LeanDescribe(id, DescribeKind.Lemma, title, leanRef, provenance, content, formula);

        public static Describe Definition(
            DescribeId id,
            Heading title,
            LeanDeclarationRef leanRef,
            DescribeProvenance provenance,
            BlockSequence content,
            Formula? formula = null) =>
            LeanDescribe(id, DescribeKind.Definition, title, leanRef, provenance, content, formula);

        public static Describe Example(
            DescribeId id,
            Heading title,
            Formula formula,
            DescribeProvenance provenance,
            BlockSequence content) =>
            new(
                id,
                DescribeKind.Example,
                title,
                DescribeStatement.FromFormula(formula),
                provenance,
                content);

        public static Describe Remark(
            DescribeId id,
            Heading title,
            DescribeStatement statement,
            DescribeProvenance provenance,
            BlockSequence content) =>
            new(id, DescribeKind.Remark, title, statement, provenance, content);

        internal static Describe ReportDerived(
            DescribeId id,
            Heading title,
            DeclarationHandle handle,
            DescribeProvenance provenance,
            BlockSequence content,
            DescribeRole? role) =>
            new(
                id,
                role switch
                {
                    DescribeRole.Definition => DescribeKind.Definition,
                    DescribeRole.Proposition => DescribeKind.Proposition,
                    DescribeRole.Lemma => DescribeKind.Lemma,
                    _ => DescribeKind.Theorem,
                },
                title,
                DescribeStatement.FromLean(LeanDeclarationRef.Create(handle.Value)),
                provenance,
                content,
                kindSource: new DescribeKindSource.ReportDerived(handle, role));

        private static Describe LeanDescribe(
            DescribeId id,
            DescribeKind kind,
            Heading title,
            LeanDeclarationRef leanRef,
            DescribeProvenance provenance,
            BlockSequence content,
            Formula? formula)
        {
            ArgumentNullException.ThrowIfNull(leanRef);
            if (ScribeDescribeContract.RequiresLatex(DescribeVocabulary.CanonicalName(kind)))
            {
                ArgumentNullException.ThrowIfNull(formula);
            }

            return new Describe(
                id,
                kind,
                title,
                DescribeStatement.FromLean(leanRef),
                provenance,
                content,
                formula);
        }
    }

    internal static BlockSequence ResolveBlocks(BlockSequence content, DeclarationCatalog catalog) =>
        BlockSequence.Create(content.Items.Select(block => block switch
        {
            Section section => new Section(section.Title, ResolveBlocks(section.Content, catalog)),
            Describe describe => describe.Resolve(catalog),
            _ => block,
        }));

    internal static bool HasReportDerived(BlockSequence content) => content.Items.Any(block => block switch
    {
        Section section => HasReportDerived(section.Content),
        Describe describe => describe.KindSource is DescribeKindSource.ReportDerived
            || HasReportDerived(describe.Content),
        _ => false,
    });

}

public sealed class ScribeDocument
{
    private ScribeDocument(
        DocumentHeader header,
        Heading title,
        BlockSequence content,
        ImmutableArray<DocumentEdge> edges)
    {
        Header = header;
        Title = title;
        Content = content;
        Edges = edges;
    }

    public DocumentHeader Header { get; }

    public Heading Title { get; }

    public BlockSequence Content { get; }

    public ImmutableArray<DocumentEdge> Edges { get; }

    public static ScribeDocument Create(
        DocumentHeader header,
        Heading title,
        BlockSequence content,
        IEnumerable<DocumentEdge>? edges = null)
    {
        ArgumentNullException.ThrowIfNull(header);
        ArgumentNullException.ThrowIfNull(title);
        ArgumentNullException.ThrowIfNull(content);
        var edgeArray = (edges ?? []).ToImmutableArray();
        if (edgeArray.Any(static edge => edge is null))
        {
            throw new ArgumentException("Document edges cannot contain null.", nameof(edges));
        }
        RequireUniqueDescribeIds(content);
        return new ScribeDocument(header, title, content, edgeArray);
    }

    internal ScribeDocument ResolveDeclarations(DeclarationCatalog catalog) =>
        new(Header, Title, DocumentBlock.ResolveBlocks(Content, catalog), Edges);

    internal bool HasReportDerivedDeclarations => DocumentBlock.HasReportDerived(Content);

    private static void RequireUniqueDescribeIds(BlockSequence content)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        Visit(content);
        return;

        void Visit(BlockSequence blocks)
        {
            foreach (var block in blocks.Items)
            {
                switch (block)
                {
                    case DocumentBlock.Section section:
                        Visit(section.Content);
                        break;
                    case DocumentBlock.Describe describe:
                        if (!seen.Add(describe.Id.Value))
                        {
                            throw new ArgumentException(
                                $"Duplicate Describe ID: {describe.Id.Value}.",
                                nameof(content));
                        }
                        Visit(describe.Content);
                        break;
                }
            }
        }
    }
}

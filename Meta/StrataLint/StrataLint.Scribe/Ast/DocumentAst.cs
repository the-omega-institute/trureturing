using System.Collections.Immutable;

namespace StrataLint.Scribe;

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
        public Describe(
            DescribeId id,
            DescribeKind kind,
            Heading title,
            DescribeStatement statement,
            DescribeProvenance provenance,
            BlockSequence content)
        {
            Id = id ?? throw new ArgumentNullException(nameof(id));
            Title = title ?? throw new ArgumentNullException(nameof(title));
            Statement = statement ?? throw new ArgumentNullException(nameof(statement));
            Provenance = provenance ?? throw new ArgumentNullException(nameof(provenance));
            Content = content ?? throw new ArgumentNullException(nameof(content));
            Kind = kind is DescribeKind.Definition
                or DescribeKind.Theorem
                or DescribeKind.Proposition
                or DescribeKind.Lemma
                or DescribeKind.Example
                or DescribeKind.Remark
                    ? kind
                    : throw new ArgumentOutOfRangeException(nameof(kind));
        }

        public DescribeId Id { get; }

        public DescribeKind Kind { get; }

        public Heading Title { get; }

        public DescribeStatement Statement { get; }

        public DescribeProvenance Provenance { get; }

        public BlockSequence Content { get; }
    }

}

public sealed class ScribeDocument
{
    private ScribeDocument(
        DocumentHeader header,
        Heading title,
        BlockSequence content)
    {
        Header = header;
        Title = title;
        Content = content;
    }

    public DocumentHeader Header { get; }

    public Heading Title { get; }

    public BlockSequence Content { get; }

    public static ScribeDocument Create(
        DocumentHeader header,
        Heading title,
        BlockSequence content)
    {
        ArgumentNullException.ThrowIfNull(header);
        ArgumentNullException.ThrowIfNull(title);
        ArgumentNullException.ThrowIfNull(content);
        RequireUniqueDescribeIds(content);
        return new ScribeDocument(header, title, content);
    }

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

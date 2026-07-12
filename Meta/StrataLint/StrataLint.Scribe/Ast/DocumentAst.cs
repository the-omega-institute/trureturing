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
        value is { Length: > 0 } && value.IndexOfAny(['\r', '\n']) < 0
            ? new TextRun(value)
            : throw new ArgumentException("Text run must be non-empty and single-line.", nameof(value));

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

    public sealed record ComputedValue(
        Heading Label,
        DeterministicComputation Computation) : DocumentBlock;

    public sealed record RenderedStatement(LeanDeclarationRef Declaration) : DocumentBlock;

    public sealed record Section(Heading Title, BlockSequence Content) : DocumentBlock;

    public sealed record Proposition(
        Heading Title,
        LeanDeclarationRef Declaration,
        BlockSequence Content) : DocumentBlock;

    public sealed record Theorem(
        Heading Title,
        LeanDeclarationRef Declaration,
        BlockSequence Content) : DocumentBlock;
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
        return new ScribeDocument(header, title, content);
    }
}

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
            DescribeKind? kind,
            Heading title,
            DescribeStatement statement,
            AssessedProvenance assessedProvenance,
            BlockSequence content,
            Formula? statementFormula = null,
            DescribeKindSource? kindSource = null,
            StatementSource? statementSource = null)
        {
            Id = id ?? throw new ArgumentNullException(nameof(id));
            Title = title ?? throw new ArgumentNullException(nameof(title));
            Statement = statement ?? throw new ArgumentNullException(nameof(statement));
            AssessedProvenance = assessedProvenance ?? throw new ArgumentNullException(nameof(assessedProvenance));
            Content = content ?? throw new ArgumentNullException(nameof(content));
            StatementFormula = statementFormula;
            StatementSource = statementSource;
            FormulaProvenance = statementSource is StatementSource.LeanDerived
                || statementSource is null
                    && statementFormula is not null
                    && statement is DescribeStatement.LeanDeclaration lean
                    && StatementProjectionFixtureLoader.IsDerivedFrom(statementFormula, lean.Value)
                ? StatementFormulaProvenance.LeanDerived : StatementFormulaProvenance.HandAuthored;
            this.kind = kind is DescribeKind.Definition
                or DescribeKind.Theorem
                or DescribeKind.Proposition
                or DescribeKind.Lemma
                or DescribeKind.Example
                or DescribeKind.Remark
                    ? kind
                    : kind is null
                        ? null
                    : throw new ArgumentOutOfRangeException(nameof(kind));
            KindSource = kindSource ?? new DescribeKindSource.Authored(
                this.kind ?? throw new InvalidOperationException("An authored Describe requires a kind."));
        }

        private readonly DescribeKind? kind;

        public DescribeId Id { get; }

        public DescribeKind Kind => kind ?? throw new InvalidOperationException(KindSource switch
        {
            DescribeKindSource.ReportDerived derived =>
                $"Report-derived Describe '{Id.Value}' for declaration '{derived.Handle.Value}' "
                + "has no narrative kind until its declaration catalog is resolved.",
            _ => $"Describe '{Id.Value}' has no narrative kind.",
        });

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
                AssessedProvenance,
                resolvedContent,
                StatementFormula,
                statementSource: StatementSource);
        }

        public Heading Title { get; }

        public DescribeStatement Statement { get; }

        public AssessedProvenance AssessedProvenance { get; }

        public DescribeProvenanceKind ProvenanceKind => DescribeVocabulary.Kind(AssessedProvenance);

        public LibraryNoteRef? LiteratureReference => AssessedProvenance is AssessedProvenance.LiteratureAttested literature
            ? literature.NoteRef
            : null;

        public ImmutableArray<LibraryNoteRef> AcknowledgementReferences => AssessedProvenance switch
        {
            AssessedProvenance.RepoDerived repository => repository.Acknowledgements,
            AssessedProvenance.SuspectedNovel novel => novel.Acknowledgements,
            _ => [],
        };

        public BlockSequence Content { get; }

        public Formula? StatementFormula { get; }

        public StatementSource? StatementSource { get; }

        public StatementFormulaProvenance FormulaProvenance { get; }

        /// <summary>
        /// A remark about a declaration, naming it by handle rather than by a hand-built reference.
        /// </summary>
        /// <remarks>
        /// A remark carries no statement source. The statement-source exclusivity exists to stop a
        /// document from restating what Lean already owns, and a remark restates nothing: it emits a
        /// reference to the declaration and prose about it, never a formula. Giving it a
        /// <see cref="StatementSource"/> would force a remark whose subject is a projectable theorem
        /// to display that theorem's statement, turning commentary into a restatement — the opposite
        /// of what the invariant is for.
        /// </remarks>
        /// <summary>
        /// A remark or example whose subject is an authored formula rather than a Lean declaration.
        /// </summary>
        /// <remarks>
        /// These nodes name nothing Lean owns, so the statement-source exclusivity has no work to do
        /// here: there is no declaration whose statement could be restated. What they carry is the
        /// author's own expression, and the provenance assessment is the same one every other node
        /// makes.
        /// </remarks>
        internal static Describe AuthoredFormula(
            DescribeId id,
            DescribeKind kind,
            Heading title,
            Formula formula,
            AssessedProvenance provenance,
            BlockSequence content) =>
            new(
                id,
                kind is DescribeKind.Remark or DescribeKind.Example
                    ? kind
                    : throw new ArgumentOutOfRangeException(
                        nameof(kind),
                        "An authored-formula Describe is a remark or an example."),
                title,
                DescribeStatement.FromFormula(formula ?? throw new ArgumentNullException(nameof(formula))),
                provenance ?? throw new ArgumentNullException(nameof(provenance)),
                content);

        internal static Describe RemarkOn(
            DescribeId id,
            DeclarationHandle handle,
            Heading title,
            AssessedProvenance provenance,
            BlockSequence content) =>
            new(
                id,
                DescribeKind.Remark,
                title,
                DescribeStatement.FromLean(LeanDeclarationRef.Create(handle.Value)),
                provenance ?? throw new ArgumentNullException(nameof(provenance)),
                content,
                statementFormula: null,
                kindSource: new DescribeKindSource.ReportDerived(handle, DescribeRole.Remark));

        internal static Describe ReportDerived(
            DescribeId id,
            Heading title,
            DeclarationHandle handle,
            StatementSource statementSource,
            AssessedProvenance provenance,
            BlockSequence content,
            DescribeRole? role)
        {
            var declaration = LeanDeclarationRef.Create(handle.Value);
            var materialized = StatementSource.Materialize(statementSource, declaration);
            return new(
                id,
                role switch
                {
                    DescribeRole.Definition => DescribeKind.Definition,
                    DescribeRole.Theorem => DescribeKind.Theorem,
                    DescribeRole.Proposition => DescribeKind.Proposition,
                    DescribeRole.Lemma => DescribeKind.Lemma,
                    null => null,
                    _ => throw new ArgumentOutOfRangeException(nameof(role)),
                },
                title,
                DescribeStatement.FromLean(declaration),
                provenance ?? throw new ArgumentNullException(nameof(provenance)),
                content,
                materialized.Formula,
                new DescribeKindSource.ReportDerived(handle, role),
                materialized.Source);
        }

    }

    internal static BlockSequence ResolveBlocks(BlockSequence content, DeclarationCatalog catalog) =>
        BlockSequence.Create(content.Items.Select(block => block switch
        {
            Section section => new Section(section.Title, ResolveBlocks(section.Content, catalog)),
            Describe describe => describe.Resolve(catalog),
            _ => block,
        }));

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

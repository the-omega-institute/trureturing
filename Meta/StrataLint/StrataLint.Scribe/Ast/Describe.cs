using System.Text.RegularExpressions;

namespace StrataLint.Scribe;

public sealed record DescribeId
{
    private static readonly Regex Pattern = new(
        "^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    private DescribeId(string value) => Value = value;

    public string Value { get; }

    public static DescribeId Create(string value) =>
        value is not null && Pattern.IsMatch(value)
            ? new DescribeId(value)
            : throw new ArgumentException("Describe ID is not canonical.", nameof(value));

    public override string ToString() => Value;
}

public enum DescribeKind
{
    Definition,
    Theorem,
    Proposition,
    Lemma,
    Example,
    Remark,
}

public enum DescribeRole { Definition, Theorem, Proposition, Lemma }

internal abstract record DescribeKindSource
{
    private DescribeKindSource() { }
    internal sealed record Authored(DescribeKind Value) : DescribeKindSource;
    internal sealed record ReportDerived(DeclarationHandle Handle, DescribeRole? Role) : DescribeKindSource;
}

public enum DescribeProvenanceKind
{
    LiteratureAttested,
    RepoDerived,
    SuspectedNovel,
    Unassessed,
}

public abstract record DescribeStatement
{
    private DescribeStatement() { }

    public sealed record FormulaAst : DescribeStatement
    {
        private FormulaAst(Formula value) =>
            Value = value ?? throw new ArgumentNullException(nameof(value));

        public Formula Value { get; }

        internal static FormulaAst Create(Formula value) => new(value);
    }

    public sealed record LeanDeclaration : DescribeStatement
    {
        private LeanDeclaration(LeanDeclarationRef value) =>
            Value = value ?? throw new ArgumentNullException(nameof(value));

        public LeanDeclarationRef Value { get; }

        internal static LeanDeclaration Create(LeanDeclarationRef value) => new(value);
    }

    public static DescribeStatement FromFormula(Formula value)
    {
        ArgumentNullException.ThrowIfNull(value);
        return FormulaAst.Create(value);
    }

    public static DescribeStatement FromLean(LeanDeclarationRef value)
    {
        ArgumentNullException.ThrowIfNull(value);
        return LeanDeclaration.Create(value);
    }
}

public sealed record DescribeProvenance
{
    private DescribeProvenance(
        DescribeProvenanceKind kind,
        LibraryNoteRef? literatureReference)
    {
        Kind = kind;
        LiteratureReference = literatureReference;
    }

    public DescribeProvenanceKind Kind { get; }

    public LibraryNoteRef? LiteratureReference { get; }

    public static DescribeProvenance LiteratureAttested(LibraryNoteRef reference)
    {
        ArgumentNullException.ThrowIfNull(reference);
        return new DescribeProvenance(
            DescribeProvenanceKind.LiteratureAttested,
            reference);
    }

    public static DescribeProvenance RepoDerived() =>
        new(DescribeProvenanceKind.RepoDerived, null);

    public static DescribeProvenance SuspectedNovel() =>
        new(DescribeProvenanceKind.SuspectedNovel, null);

    public static DescribeProvenance Unassessed() =>
        new(DescribeProvenanceKind.Unassessed, null);
}

public abstract record AssessedProvenance
{
    private AssessedProvenance() { }
    public sealed record RepoDerived : AssessedProvenance;
    public sealed record LiteratureAttested(LibraryNoteRef NoteRef) : AssessedProvenance;
    public sealed record SuspectedNovel(GidRef SearchReceipt) : AssessedProvenance;

    public static AssessedProvenance FromRepo() => new RepoDerived();
    public static AssessedProvenance FromLiterature(LibraryNoteRef noteRef) =>
        new LiteratureAttested(noteRef ?? throw new ArgumentNullException(nameof(noteRef)));
    public static AssessedProvenance NovelAfterSearch(GidRef searchReceipt) =>
        new SuspectedNovel(searchReceipt ?? throw new ArgumentNullException(nameof(searchReceipt)));

    internal DescribeProvenance ToLegacy() => this switch
    {
        RepoDerived => DescribeProvenance.RepoDerived(),
        LiteratureAttested value => DescribeProvenance.LiteratureAttested(value.NoteRef),
        SuspectedNovel => DescribeProvenance.SuspectedNovel(),
        _ => throw new InvalidOperationException("Unknown assessed provenance."),
    };
}

public static class Describe
{
    public static DocumentBlock.Describe Lean(
        DescribeId id,
        DeclarationHandle handle,
        Heading title,
        AssessedProvenance provenance,
        BlockSequence narrative,
        DescribeRole? role = null) =>
        DocumentBlock.Describe.ReportDerived(
            id, title, handle,
            (provenance ?? throw new ArgumentNullException(nameof(provenance))).ToLegacy(),
            narrative, role);
}

internal static class DescribeVocabulary
{
    internal static string HeadingName(DescribeKind kind) => kind switch
    {
        DescribeKind.Definition => "Definition",
        DescribeKind.Theorem => "Theorem",
        DescribeKind.Proposition => "Proposition",
        DescribeKind.Lemma => "Lemma",
        DescribeKind.Example => "Example",
        DescribeKind.Remark => "Remark",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };

    internal static string CanonicalName(DescribeKind kind) => kind switch
    {
        DescribeKind.Definition => "definition",
        DescribeKind.Theorem => "theorem",
        DescribeKind.Proposition => "proposition",
        DescribeKind.Lemma => "lemma",
        DescribeKind.Example => "example",
        DescribeKind.Remark => "remark",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };

    internal static string CanonicalName(DescribeProvenanceKind provenance) => provenance switch
    {
        DescribeProvenanceKind.LiteratureAttested => "literature-attested",
        DescribeProvenanceKind.RepoDerived => "repo-derived",
        DescribeProvenanceKind.SuspectedNovel => "suspected-novel",
        DescribeProvenanceKind.Unassessed => "unassessed",
        _ => throw new ArgumentOutOfRangeException(nameof(provenance)),
    };
}

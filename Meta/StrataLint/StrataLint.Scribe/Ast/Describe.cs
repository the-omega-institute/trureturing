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

public enum DescribeRole { Definition, Theorem, Proposition, Lemma, Remark }

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

}

public sealed record ProjectionGap
{
    internal ProjectionGap(
        string reasonCode,
        string offendingSubject,
        string projectorEpoch,
        string declarationContentDigest)
    {
        ReasonCode = reasonCode;
        OffendingSubject = offendingSubject;
        ProjectorEpoch = projectorEpoch;
        DeclarationContentDigest = declarationContentDigest;
    }

    public string ReasonCode { get; }
    public string OffendingSubject { get; }
    public string ProjectorEpoch { get; }
    public string DeclarationContentDigest { get; }
}

public abstract record StatementSource
{
    private StatementSource() { }

    public sealed record LeanDerived : StatementSource;

    public sealed record Authored : StatementSource
    {
        internal Authored(Formula presentation, ProjectionGap? projectionGap)
        {
            Presentation = presentation ?? throw new ArgumentNullException(nameof(presentation));
            ProjectionGap = projectionGap;
        }

        public Formula Presentation { get; }
        public ProjectionGap? ProjectionGap { get; }
    }

    /// <summary>
    /// The node names its Lean declaration and displays no statement formula. Legal only where the
    /// projector cannot supply one, exactly like <see cref="Authored"/>: whether to author a
    /// presentation or to show none is a presentation choice, and it is the author's to make only
    /// where Lean owns nothing to restate.
    /// </summary>
    public sealed record NoFormula : StatementSource
    {
        internal NoFormula(ProjectionGap? projectionGap) => ProjectionGap = projectionGap;

        public ProjectionGap? ProjectionGap { get; }
    }

    public static StatementSource FromLean() => new LeanDerived();
    public static StatementSource FromAuthor(Formula presentation) => new Authored(presentation, null);
    public static StatementSource WithoutFormula() => new NoFormula(null);

    internal static (StatementSource Source, Formula? Formula) Materialize(
        StatementSource source,
        LeanDeclarationRef declaration)
    {
        ArgumentNullException.ThrowIfNull(source);
        var assessment = StatementProjectionFixtureLoader.Assess(declaration);
        return (source, assessment.Outcome) switch
        {
            (LeanDerived, ProjectionOutcome.Projected projected) => (source, projected.Formula),
            (LeanDerived, ProjectionOutcome.Unprojectable failed) => throw new InvalidOperationException(
                $"Lean-derived statement is unavailable for {declaration.Value}: {failed.Reason}"),
            (Authored, ProjectionOutcome.Projected) => throw new InvalidOperationException(
                $"Authored statement is illegal because Lean projection is available for {declaration.Value}."),
            (Authored authored, ProjectionOutcome.Unprojectable failed) =>
                (new Authored(authored.Presentation, Gap(failed, assessment)), authored.Presentation),
            (NoFormula, ProjectionOutcome.Projected) => throw new InvalidOperationException(
                $"Omitting the statement is illegal because Lean projection is available for {declaration.Value}."),
            (NoFormula, ProjectionOutcome.Unprojectable failed) =>
                (new NoFormula(Gap(failed, assessment)), null),
            _ => throw new InvalidOperationException("Unknown statement source or projection outcome."),
        };
    }

    private static ProjectionGap Gap(
        ProjectionOutcome.Unprojectable failed,
        StatementProjectionFixtureLoader.Assessment assessment) =>
        new(StatementProjectionFixtureLoader.ReasonCode(failed.Reason),
            StatementProjectionFixtureLoader.OffendingSubject(failed.Reason),
            StatementProjectionFixtureLoader.ProjectorEpoch,
            assessment.DeclarationContentDigest);
}

internal abstract record DescribeProvenanceSource
{
    private DescribeProvenanceSource() { }

    internal sealed record Legacy(DescribeProvenance Value) : DescribeProvenanceSource;
    internal sealed record Assessed(AssessedProvenance Value) : DescribeProvenanceSource;
}

public static class Describe
{
    public static DocumentBlock.Describe Lean(
        DescribeId id,
        DeclarationHandle handle,
        Heading title,
        StatementSource statementSource,
        AssessedProvenance provenance,
        BlockSequence narrative,
        DescribeRole? role = null) =>
        DocumentBlock.Describe.ReportDerived(
            id, title, handle, statementSource,
            provenance ?? throw new ArgumentNullException(nameof(provenance)),
            narrative, role);

    /// <summary>
    /// Commentary about a declaration, named by handle. Emits a reference and prose, never a formula,
    /// so it takes no <see cref="StatementSource"/> — see <c>DocumentBlock.Describe.RemarkOn</c>.
    /// </summary>
    public static DocumentBlock.Describe Remark(
        DescribeId id,
        DeclarationHandle handle,
        Heading title,
        AssessedProvenance provenance,
        BlockSequence narrative) =>
        DocumentBlock.Describe.RemarkOn(id, handle, title, provenance, narrative);
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

    internal static DescribeProvenanceKind Kind(AssessedProvenance provenance) => provenance switch
    {
        AssessedProvenance.LiteratureAttested => DescribeProvenanceKind.LiteratureAttested,
        AssessedProvenance.RepoDerived => DescribeProvenanceKind.RepoDerived,
        AssessedProvenance.SuspectedNovel => DescribeProvenanceKind.SuspectedNovel,
        _ => throw new InvalidOperationException("Unknown assessed provenance."),
    };
}

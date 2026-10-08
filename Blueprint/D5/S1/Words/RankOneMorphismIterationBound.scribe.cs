using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class RankOneMorphismIterationBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/RankOneMorphismIterationBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/filimonovapuzynina2026abelianperiodicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A primitive binary rank-one morphism has an effective bounded criterion for eventual abelian periodicity.",
        H("Effective iteration bound for binary rank-one morphisms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("effective-iteration-bound"),
                DeclarationHandle.Create(Prefix + "effective_iteration_bound"),
                H("The bounded source criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every actual nonerasing, prolongable, primitive binary morphism "
                    + "of rank one and every actual all-iterate fixed word x, eventual "
                    + "abelian periodicity with arbitrary finite preperiod is equivalent "
                    + "to the original four-word cyclic block witness at some "
                    + "1 ≤ K ≤ 2^((f 0).length + (f 1).length). The witness uses exact "
                    + "Parikh equality and nonempty common-vector blocks on both complete "
                    + "rotations."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("filimonova-puzynina-2026-rank-one-iteration-bound"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("finite-checker-uap"),
                DeclarationHandle.Create(Prefix + "finiteChecker_uap"),
                H("Executable finite checker"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The executable finite-image checker returns true exactly when the "
                    + "actual fixed word is ultimately abelian periodic on the same "
                    + "complete source domain. Leading-zero digits, alternating and "
                    + "unary edge cases, and arbitrary preperiods remain in scope."))),
                DescribeRole.Theorem))));
}

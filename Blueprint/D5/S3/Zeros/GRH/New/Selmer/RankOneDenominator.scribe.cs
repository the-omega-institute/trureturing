using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class RankOneDenominatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank One Denominator", H("Rank One Denominator"),
        Blocks(
            Paragraph(Text("Rank-one denominator bound for test forms by averaging over classes of U(1).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/RankOneDenominator.rank_one_bound"),
                H("rank_one_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the line spanned by the lift Y.trivialLift from U(1) have denominator ≤ β at ι, and U(1) have trivial stabilisers and h' classes at principal level at the chosen places. Then test forms at ℓ satisfy ‖ι(h'⟨Ξ, pr Ξ'⟩)‖ ≤ e^β, pr projecting orthogonally onto that line.")))))));
}

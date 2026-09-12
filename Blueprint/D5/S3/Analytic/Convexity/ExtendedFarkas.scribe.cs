using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class ExtendedFarkasDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/dvorak2024duality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Farkas alternative holds for extended coefficients under four infinity restrictions.",
        H("Extended Farkas Alternative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("extended-farkas-alternative"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/ExtendedFarkas.extended_farkas"),
                H("Alternative for extended coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let F be a linearly ordered field and I and J arbitrary finite types, with decidable equality on I. Extend F is WithBot (WithTop F). Negative infinity absorbs every sum. The action of every nonnegative scalar on negative infinity is negative infinity; zero acting on positive infinity is zero, and a positive scalar acting on positive infinity is positive infinity. Finite coefficients use ordinary field multiplication.")),
                    Paragraph(Text("For A : Matrix I J (Extend F) and b : I → Extend F, assume that no row of A contains both infinities, no column contains both infinities, no row containing positive infinity has a positive-infinite bound, and no row containing negative infinity has a negative-infinite bound.")),
                    Paragraph(Text("Exactly one alternative holds: there exists x : J → NNeg F with A ₘ* x ≤ b; or there exists y : I → NNeg F with −Aᵀ ₘ* y ≤ 0 and b ᵥ⬝ y < 0. Each heterogeneous product is the finite sum of the nonnegative weights acting on the extended coefficients.")),
                    Paragraph(Text("The construction removes tautological rows and columns forced to zero, applies the finite inequality alternative to the remaining field coefficients, and restores witnesses in both directions. The infinity restrictions justify the zero weights and the restored inequalities."))),
                DescribeRole.Theorem))));
}

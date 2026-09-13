using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class FiniteStrongDualityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/dvorak2024duality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both feasible valid extended linear programs attain finite opposite values.",
        H("Finite Attainment for Extended Linear Programs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("both-feasible-strong-duality"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/FiniteStrongDuality.strong_duality_of_both_feasible"),
                H("Finite opposite attained values"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let F be a linearly ordered field and I and J arbitrary finite row and column types with decidable equality. An ExtendedLP contains a matrix A, bound vector b and objective vector c with coefficients in Extend F; its variables are nonnegative elements of F. It minimizes the sum c ᵥ⬝ x subject to A ₘ* x ≤ b.")),
                    Paragraph(Text("ValidELP requires all six restrictions: no row or column of A mixes the two infinities; a negative-infinite bound cannot share a row with a negative-infinite matrix entry; a negative-infinite objective coefficient cannot share a column with a positive-infinite matrix entry; a positive-infinite bound cannot share a row with a positive-infinite matrix entry; and a positive-infinite objective coefficient cannot share a column with a negative-infinite matrix entry.")),
                    Paragraph(Text("Dualization sends (A,b,c) to (−Aᵀ,c,b). A program is feasible when it reaches some extended objective value other than positive infinity. If a valid program P and its dual are both feasible, there exists r : F such that P reaches the finite value toE(−r) and its dual reaches the finite value toE(r). Reaches includes an actual feasible vector realizing the indicated objective value.")),
                    Paragraph(Text("The augmented system constructs primal and dual witnesses whose finite objectives sum to at most zero. Weak duality supplies the opposite inequality, giving equality and the stated opposite values. The proof retains the recession argument needed to exclude a zero scaling coefficient in the augmented alternative."))),
                DescribeRole.Theorem))));
}

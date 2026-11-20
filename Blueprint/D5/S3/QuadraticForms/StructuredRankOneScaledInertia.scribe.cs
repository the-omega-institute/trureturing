using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class StructuredRankOneScaledInertiaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/StructuredRankOneScaledInertia.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mazhang2026scaleddowndate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inertia of A − t w wᵀ/Δ is In(A) − In([Δ]) + In([(1 − t)Δ]) for every real t.",
        H("Coefficient-dependent inertia of the structured downdate"),
        Blocks(
            Describe.Lean(DescribeId.Create("scaled-downdate-def"),
                DeclarationHandle.Create(Prefix + "scaledDowndate"), H("The scaled downdate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("M_t = A − t w wᵀ/Δ with w = A x and Δ = xᵀ A x."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scaled-downdate-inertia"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Inertia of the scaled downdate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let A be real symmetric and x a vector with Δ = xᵀ A x ≠ 0, and put w = A x. For "
                        + "every real t the matrix M_t = A − t w wᵀ/Δ is symmetric, and with [P] equal to 1 "
                        + "when P holds and 0 otherwise: n₊(M_t) + [Δ > 0] = n₊(A) + [(1 − t)Δ > 0], "
                        + "n₋(M_t) + [Δ < 0] = n₋(A) + [(1 − t)Δ < 0], and n₀(M_t) = n₀(A) + [t = 1]. "
                        + "Hence for t < 1 the inertia of M_t equals that of A; M_1 is the structured "
                        + "downdate; and for t > 1 the nullity is unchanged while one eigenvalue moves from "
                        + "the sign of Δ to the opposite sign.")),
                    Paragraph(Text(
                        "For t = 0 nothing changes. For t ≠ 0 put d = Δ/t and c = d − Δ. The block matrix "
                        + "A ⊕ [c] is congruent, by the unipotent matrix with x in its corner column, to the "
                        + "bordered matrix with off-diagonal block w and corner Δ + c = d. Eliminating w with "
                        + "the pivot d makes that bordered matrix congruent to (A − w wᵀ/d) ⊕ [d], and "
                        + "A − w wᵀ/d = M_t. Sylvester's law of inertia and additivity over blocks give "
                        + "n₊(A) + [c > 0] = n₊(M_t) + [d > 0] and the same for n₋. Since c = (1 − t)Δ/t, "
                        + "the sign cases t > 0 and t < 0 both give the stated identities, and the nullity "
                        + "follows because the three counts add to n. This is Corollary 4 of H. Ma and "
                        + "W. Zhang (DOI 10.5281/zenodo.23920598) on MathOverflow 513954, revision 2, "
                        + "asked by Lucid."))),
                DescribeRole.Theorem))));
}

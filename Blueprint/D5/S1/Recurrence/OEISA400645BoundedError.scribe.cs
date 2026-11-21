using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class OEISA400645BoundedErrorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/OEISA400645BoundedError.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a400645siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every A400645 source sequence satisfies a_n = c λ^n + O(1) with c > 0, and "
            + "a_(n+1)/a_n = λ + O(λ^(-n)).",
        H("Bounded absolute error and ratio rate for A400645"),
        Blocks(
            Describe.Lean(DescribeId.Create("a400645-bounded-error"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Bounded error and ratio rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let a be any sequence satisfying the A400645 source conditions of the "
                        + "frozen module D5/S1/Recurrence/OEISA400645, let r be its squared "
                        + "limit, the largest real root of y^4 − y^3 − y^2 − y + 1, and let "
                        + "λ = √r be the limiting ratio. Then there is c > 0 with "
                        + "a_n − c λ^n = O(1) and a_(n+1)/a_n − λ = O(λ^(−n)) as n → ∞.")),
                    Paragraph(Text(
                        "Proof. Put B_j = a_(j+23)^2. The rounding step a_(n+1) = round √s_n "
                        + "gives |a_(n+1)^2 − s_n| ≤ 2 a_n, so B_j − B_(j+1) − B_(j+2) − "
                        + "B_(j+3) + B_(j+4) = e_j with |e_j| ≤ 2 a_(j+26). The frozen module "
                        + "gives B_j / r^j → L > 0, hence B_j ≤ (L + 1) r^j eventually and "
                        + "e_j = O(r^(j/2)). The characteristic polynomial factors as "
                        + "(y^2 − β y + 1)(y^2 − (1 − β) y + 1) with β = (1 + √13)/2. The "
                        + "first factor has the roots r and β − r = 1/r; the second has "
                        + "discriminant (1 − β)^2 − 4 < 0 and its roots lie on the unit "
                        + "circle. So r is a simple root, its derivative being positive at r, "
                        + "and every other root has modulus below √r. Dominant-root forcing "
                        + "(D5/S1/Recurrence/Asymptotic/DominantRootForcing) at q = √r, "
                        + "with B_j − L r^j = o(r^j), gives B_j = L r^j + O(r^(j/2)).")),
                    Paragraph(Text(
                        "Write x = a_(j+23) and y = √L λ^j. Then (x − y)(x + y) = "
                        + "B_j − L r^j = O(λ^j) and x + y ≥ y, so |x − y| = O(1). With "
                        + "c = √L / λ^23 this is a_n − c λ^n = O(1). For the ratio, "
                        + "a_(n+1) − λ a_n = (a_(n+1) − c λ^(n+1)) − λ (a_n − c λ^n) is "
                        + "bounded, and a_n ≥ c λ^n / 2 once c λ^n is at least twice the "
                        + "error bound; dividing gives a_(n+1)/a_n − λ = O(λ^(−n)).")),
                    Paragraph(Text(
                        "This is Corollary 3 in Section 4 of H. Ma and W. Zhang's note on "
                        + "OEIS A400645 (DOI 10.5281/zenodo.24369110). Here it holds for every "
                        + "sequence meeting the source conditions; the frozen module shows "
                        + "that this sequence is unique."))),
                DescribeRole.Theorem))));
}

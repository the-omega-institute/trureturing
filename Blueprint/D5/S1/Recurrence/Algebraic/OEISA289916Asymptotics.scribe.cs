using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class OEISA289916AsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/OEISA289916Asymptotics.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a400645siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of Barker's generating function for A289916 satisfy "
            + "v_n = D r^n + O(1) with D > 0, and v_(n+1)/v_n = r + O(r^(−n)).",
        H("Asymptotics of Barker's generating function for A289916"),
        Blocks(
            Describe.Lean(DescribeId.Create("a289916-asymptotics"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Bounded error and ratio rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let v be an integer sequence whose generating function times "
                        + "(1 − z + z^2)Q(z) equals (1 + z)^2(1 − z + z^2 − z^3 + z^4 − z^5 + "
                        + "z^6), where Q(z) = z^4 − z^3 − z^2 − z + 1, and let r be the "
                        + "largest real root of Q. Then there is D > 0 with v_n − D r^n = O(1) "
                        + "and v_(n+1)/v_n − r = O(r^(−n)).")),
                    Paragraph(Text(
                        "Proof. The numerator has degree eight, so for j ≥ 0 the coefficient "
                        + "identity gives v_(j+3) − 2v_(j+4) + v_(j+5) − v_(j+6) + v_(j+7) − "
                        + "2v_(j+8) + v_(j+9) = 0: the shifted sequence u_j = v_(j+3) is "
                        + "annihilated by P(S) for the shift S and P = X^6 − 2X^5 + X^4 − X^3 + "
                        + "X^2 − 2X + 1. With β = (1 + √13)/2 and t = 1 − β, P factors as "
                        + "(X^2 − βX + 1)(X^2 − tX + 1)(X^2 − X + 1). Its roots are r, β − r = "
                        + "1/r, t/2 ± i(1 − t^2/4)^(1/2) and 1/2 ± i√3/2; these six are "
                        + "distinct, so they are all the roots and each is simple. Every root "
                        + "but r has modulus at most one.")),
                    Paragraph(Text(
                        "For a complex polynomial p with simple roots z_1, …, z_k, the "
                        + "Lagrange basis polynomials ℓ_i sum to one, and (X − z_i) ℓ_i is a "
                        + "constant multiple of the nodal polynomial, hence of p. So any u with "
                        + "p(S)u = 0 splits as u = Σ ℓ_i(S)u, where each ℓ_i(S)u is annihilated "
                        + "by S − z_i and is therefore α_i z_i^j. Applied to P, this gives "
                        + "u_j − α_r r^j = Σ over the other roots of α_z z^j, which is bounded "
                        + "by the sum of the |α_z|. Taking real parts, v_n = D r^n + O(1) with "
                        + "D = Re(α_r)/r^3. The frozen strict increase gives v_n ≥ v_0 + n, so "
                        + "D ≤ 0 would make v bounded above; hence D > 0. Finally "
                        + "v_(n+1) − r v_n = (v_(n+1) − D r^(n+1)) − r (v_n − D r^n) is bounded "
                        + "and v_n ≥ D r^n / 2 once D r^n is at least twice the error bound, so "
                        + "v_(n+1)/v_n − r = O(r^(−n)).")),
                    Paragraph(Text(
                        "This is the asymptotic clause of Corollary 8 in Section 5 of H. Ma "
                        + "and W. Zhang's note on OEIS A400645 (DOI 10.5281/zenodo.24369110); "
                        + "the strict increase is the frozen module "
                        + "D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease. The generating "
                        + "function is Colin Barker's in A289916, and r is the constant of "
                        + "A289917. The error O(1) is not improved here: numerically "
                        + "v_n − D r^n keeps oscillating with amplitude about one, mostly a "
                        + "period-six pattern from the sixth roots of unity, and D ≈ 1.5392 is "
                        + "the residue −N(1/r)/((1/r) den′(1/r)) of the generating function; "
                        + "neither the explicit value nor the failure of o(1) is formalized."))),
                DescribeRole.Theorem))));
}

using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class ChapotonConjectureFiveFourRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refutes only printed equation 5.5, Conjecture 5.4 in arXiv:2001.01449v1, "
            + "at n = 2; literature-attested, new_counterexample_claimed = false. "
            + "No claim that the authors' intended proposition is false or its proof has "
            + "a gap; the corrected version proved in later literature is outside scope. "
            + "No verdict on Proposition 5.2. No priority is claimed for the determinant "
            + "value or identification of this off-by-one.",
        H("Chapoton and Han Conjecture 5.4 printed formula refutation"),
        Blocks(
            Paragraph(Text(
                "Frédéric Chapoton and Guo-Niu Han, On the roots of the Poupard and Kreweras "
                    + "polynomials, arXiv:2001.01449v1, printed page 9, Conjecture 5.4, "
                    + "equation 5.5, says For all n >= 0. The preceding definition has "
                    + "inclusive bounds 0 <= i <= n and 0 <= j <= n, so the literal matrix "
                    + "has order n plus 1. The following example, equation 5.6, is labelled "
                    + "M_6 but prints six rows and six columns. These are incompatible "
                    + "index conventions on the same page. The preceding words Assuming "
                    + "this conjecture refer to Conjecture 5.3, the divisibility assertion; "
                    + "they impose no exclusion of n = 2. The formal claim keeps the full "
                    + "natural-number quantifier and uses the printed factorial product, "
                    + "with exponent 2 at odd k and 4 at even k. Empty products are one. "
                    + "The rendered original PDF pages 2, 3, 7 and 9 were checked on "
                    + "2026-09-10.")),
            Describe.Lean(
                DescribeId.Create("printed-conjecture-five-four-refuted"),
                DeclarationHandle.Create(
                    "D5/S0/Certificates/ChapotonConjectureFiveFourRefutation.result"),
                H("The printed factorial product fails at n = 2"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operator is defined by equation 2.1 at D = 0. Section 5.1 on "
                        + "page 7 defines rho as the constant term after floor(d/2) iterations "
                        + "on the fixed index space. The index of x to power i times "
                        + "(1+x) to power j is 2i+j, including outer zero coefficients. "
                        + "In particular rho(c(1+x)) = c, since the index is one and there "
                        + "are zero steps. No global linearity across different indices is "
                        + "assumed. Rational scaling implements the entry formula without "
                        + "assuming global integrality; all witness divisions are exact. "
                        + "Recomputing the nine rho values gives rows (1,1,2), (1,2,6), "
                        + "(2,8,36). Division of column j by 2 to power floor(j/2) yields "
                        + "rows (1,1,1), (1,2,3), (2,8,18), whose determinant is 4. "
                        + "Equation 5.5 at n = 2 instead requires the square of 1!, namely 1. "
                        + "The kernel derivation uses Mathlib monic polynomial division, "
                        + "explicit polynomial identities checked by ring, determinant "
                        + "expansion and norm_num. No frozen numerical theorem or external "
                        + "oracle is used; all finite calculations are proof-local. "
                        + "Independent integer checks use equation 2.1 with polynomial "
                        + "long division and Leibniz expansion, and equation 2.2 with "
                        + "symmetric-basis geometric products and Bareiss elimination. "
                        + "All 36 printed entries agree, as do d_0 and d_1, the printed "
                        + "six-by-six determinant 2751882854400, and the page 7 rho example. "
                        + "All 770 divisions have verified zero remainder, without floating "
                        + "point. The theorem is produced by its own live numerical "
                        + "computation rather than by instantiating an earlier result. "
                        + "This is a literature-attested correction: Guo-Niu Han, Dilated "
                        + "Hankel determinants, arXiv:2607.08279v1, section 26, pages 80-84. "
                        + "Equation 26.2 on page 81 defines an N by N matrix with indices "
                        + "0 through N minus 1. Theorem 26.1, equation 26.4, proves the "
                        + "factorial product for N >= 1; its proof appears on page 84. "
                        + "Remark 26.4 on page 82 also proves the divisibility. The later "
                        + "paper silently changes the index bound and does not explicitly "
                        + "announce an erratum. new_counterexample_claimed = false. "
                        + "Only printed equation 5.5 at n = 2 is refuted. No claim is made "
                        + "that the authors' intended proposition is false or that its "
                        + "proof has a gap. The corrected version proved in later literature "
                        + "is outside this module's scope. No verdict is given on the same "
                        + "paper's Proposition 5.2, which is a separate question. Neither "
                        + "first discovery of the determinant value nor first identification "
                        + "of this off-by-one is claimed. FromRepo records this repository's "
                        + "formal derivation because no LibraryNoteRef for these papers is "
                        + "present; it does not assert literature novelty, and no L-plane "
                        + "note is introduced."))),
                DescribeRole.Theorem)),
        [],
        anchors:
        [
            Anchor.ParseCanonical("mathlib/module/Mathlib.Algebra.Polynomial.Div"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Factorial.Basic"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Tactic.NormNum"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Tactic.Ring")
        ]));
}

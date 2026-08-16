using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class MixedExclusionSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Colored nearest-neighbor exclusion has a quadratic law and a fermionic trace term.",
        H("Mixed Exclusion Spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-exclusion-recurrence-and-two-color-spectrum"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/MixedExclusionSpectrum."
                    + "mixed_exclusion_recurrence_and_two_color_spectrum"),
                H("Colored exclusion has a quadratic transfer law"),
                StatementSource.FromAuthor(MixedExclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A_m(K) be the weighted count of occupied subsets of K consecutive "
                        + "positions with no adjacent occupied pair, where each occupied position "
                        + "has m possible colors. Splitting on the last position gives "
                        + "A_m(K+2) = A_m(K+1) + m A_m(K). The corresponding two-state transfer "
                        + "matrix therefore has characteristic polynomial X^2 - X - m.")),
                    Paragraph(Text(
                        "For m = 2, retaining the two colors as separate states gives the explicit "
                        + "three-state transfer matrix with spectrum {2, -1, 0}. A rational "
                        + "eigenbasis conjugates it to that diagonal matrix, so conjugation "
                        + "invariance of trace yields tr(M^n) - 2^n = (-1)^n for positive n.")),
                    Paragraph(Text(
                        "The recurrence is a direct specialization of the repository theorem "
                        + "wordSum_succ_succ. Pinned Mathlib was searched before proving; no theorem "
                        + "packaging the two-color spectrum and trace identity was found. The proof "
                        + "uses spectrum.units_conjugate, spectrum_diagonal, Units.conj_pow, and "
                        + "Matrix.trace_units_conj.")),
                    Paragraph(Text(
                        "This formalizes the mixed-law and m = 2 degeneracy clauses of source theorem "
                        + "6.50. The k-bonacci ladder, Shannon-capacity identifications, numerical RLL "
                        + "comparisons, and physical dictionary are not asserted by this declaration."))),
                DescribeRole.Theorem))));

    private static Formula MixedExclusionFormula()
    {
        Formula m = F.Id("m");
        Formula k = F.Id("K");
        Formula n = F.Id("n");
        Formula x = F.Id("X");
        Formula count = F.Id("A");
        Formula transfer = F.Id("T");
        Formula twoColor = F.Id("M");

        Formula CountAt(Formula index) => Seq(count, Underscore, m, Open, index, Close);

        return Disp(Seq(
            Forall, Sp, m, Comma, k, Comma, n, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Esc,
            n, Gt, D(0), Sp, Rightarrow, Esc,
            CountAt(Seq(k, Plus, D(2))), Eq,
            CountAt(Seq(k, Plus, D(1))), Plus, m, CountAt(k), Sp, Land, Esc,
            Operatorname, Grp(F.Id("charpoly")), Open,
            Seq(transfer, Underscore, m), Close, Open, x, Close, Eq,
            x, Caret, Grp(D(2)), Minus, x, Minus, m, Sp, Land, Esc,
            Operatorname, Grp(F.Id("Spec")), Open, twoColor, Close, Eq,
            OpenBrace, D(2), Comma, Minus, D(1), Comma, D(0), CloseBrace, Sp, Land, Esc,
            Operatorname, Grp(F.Id("tr")), Open,
            twoColor, Caret, n, Close, Minus, D(2), Caret, n, Eq,
            Open, Minus, D(1), Close, Caret, n, Dot));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Observation;

internal sealed class FiniteWindowCRTIndistinguishabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite coprime residue window is realized by a natural-number shift, with an explicit three-modulus certificate.",
        H("Finite-Window CRT Indistinguishability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-window-cannot-separate-a-shift"),
                DeclarationHandle.Create(
                    "D5/S0/Observation/FiniteWindowCRTIndistinguishability."
                        + "finite_window_cannot_separate_shift"),
                H("A finite coprime window cannot separate a shift"),
                StatementSource.FromAuthor(IndistinguishabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite collection of positive pairwise-coprime natural moduli, "
                            + "the window-reading map is onto the dependent product of the "
                            + "corresponding residue rings. Thus one natural number realizes "
                            + "every prescribed residue in the window simultaneously.")),
                    Paragraph(Text(
                        "The construction chooses natural representatives for the target residues, "
                            + "applies the finite Chinese remainder theorem, and then identifies "
                            + "the resulting congruences with equality in each ZMod component. "
                            + "The witness depends on both the finite window and the target; no "
                            + "single shift is asserted to realize all windows at once."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-nine-twenty-five-window-certificate"),
                DeclarationHandle.Create(
                    "D5/S0/Observation/FiniteWindowCRTIndistinguishability."
                        + "window_4_9_25_certificate"),
                H("The four-nine-twenty-five window has an explicit certificate"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The product of the residue rings modulo four, nine, and twenty-five has "
                            + "exactly nine hundred elements. The natural number 511 reads as "
                            + "3 modulo 4, 7 modulo 9, and 11 modulo 25.")),
                    Paragraph(Text(
                        "This supplies one concrete realization in a pairwise-coprime observation "
                            + "window. It is an existence certificate, not a uniqueness claim and "
                            + "not a replacement for the general surjectivity theorem."))),
                DescribeRole.Lemma))));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula InWindow(Formula value, Formula window) =>
        Seq(value, Sp, InMacro, Sp, window);

    private static Formula PositiveModuli(Formula window)
    {
        Formula modulus = F.Id("m");
        return Seq(
            Forall, Sp, modulus, Comma, Sp,
            InWindow(modulus, window), Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, modulus);
    }

    private static Formula PairwiseCoprime(Formula window)
    {
        Formula first = F.Id("m");
        Formula second = F.Id("n");
        return Seq(
            Forall, Sp, first, Comma, Sp, second, Comma, Sp,
            Open,
            InWindow(first, window), Sp, Land, Sp,
            InWindow(second, window), Sp, Land, Sp,
            first, Sp, Neq, Sp, second,
            Close, Sp, Rightarrow, Sp,
            Call("Coprime", first, second));
    }

    private static Formula IndistinguishabilityFormula()
    {
        Formula window = F.Id("W");
        return Disp(Seq(
            Forall, Sp, window, Colon, Sp,
            Call("Finset", NaturalNumbers()), Comma, Sp,
            Open,
            PositiveModuli(window), Sp, Land, Sp,
            PairwiseCoprime(window),
            Close, Sp, Rightarrow, Sp,
            Call("Surjective", Call("windowReading", window)), Dot));
    }

    private static Formula Congruence(Formula value, Formula residue, Formula modulus) =>
        Seq(
            value, Sp, Equiv, Sp, residue, Sp,
            Open, Operatorname, Grp(F.Id("mod")), Sp, modulus, Close);

    private static Formula CertificateFormula()
    {
        Formula residueSpace = Seq(
            Call("ZMod", D(4)), Sp, Times, Sp,
            Call("ZMod", D(9)), Sp, Times, Sp,
            Call("ZMod", D(2, 5)));

        return Disp(Seq(
            Call("card", residueSpace), Sp, Eq, Sp, D(9, 0, 0), Sp, Land, Sp,
            Congruence(D(5, 1, 1), D(3), D(4)), Sp, Land, Sp,
            Congruence(D(5, 1, 1), D(7), D(9)), Sp, Land, Sp,
            Congruence(D(5, 1, 1), D(1, 1), D(2, 5)), Dot));
    }
}

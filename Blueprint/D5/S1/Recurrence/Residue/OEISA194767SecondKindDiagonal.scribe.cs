using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class OEISA194767SecondKindDiagonalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a189733siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth diagonal of the A194767 second-kind array has reduced denominators "
            + "(m + 1)(m + 2)/gcd(3, m + 2), and its numerators are A146535 at the shifted index.",
        H("The fourth diagonal of the A194767 second-kind array"),
        Blocks(
            Describe.Lean(DescribeId.Create("a194767-fourth-diagonal"),
                DeclarationHandle.Create(Prefix + "C3"),
                H("The fourth diagonal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The second-kind array is C(m, n) = 2B(m, n + 1) − B(m, n), where B is "
                    + "Curtz's rational array. Its fourth diagonal is C(m, m + 3) = "
                    + "2B(m, m + 4) − B(m, m + 3), written with the frozen upper entries "
                    + "triangle m 4 and triangle m 3."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a194767-fourth-diagonal-denominator"),
                DeclarationHandle.Create(Prefix + "d"),
                H("Its reduced denominators"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "d_m is the reduced positive denominator of C(m, m + 3)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a194767-a051176"),
                DeclarationHandle.Create(Prefix + "A051176"),
                H("A051176"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A051176(r) = r/gcd(r, 3) from offset 0: r/3 when 3 divides r, "
                    + "and r otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a194767-a146535"),
                DeclarationHandle.Create(Prefix + "A146535"),
                H("A146535"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A146535(r) is the reduced numerator of (2r − 1)/3, indexed from r = 1. "
                    + "The value at r = 0 is not used."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a194767-a306368"),
                DeclarationHandle.Create(Prefix + "A306368"),
                H("A306368"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A306368(r) is the reduced numerator of (r + 3)(r + 4)/((r + 1)(r + 2)), "
                    + "from offset 0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a194767-fourth-diagonal-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Value, denominators and the numerator index correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every m ≥ 0, C(m, m + 3) = (−1)^{m+1}(2m + 1)/((m + 1)(m + 2)) and "
                    + "d_m = (m + 1)(m + 2)/gcd(3, m + 2). For every k ≥ 0, "
                    + "(d_{3k}, d_{3k+1}, d_{3k+2}) = ((3k + 1)(3k + 2), (k + 1)(3k + 2), "
                    + "3(k + 1)(3k + 4)). The integer power series of d_m times (1 − z³)³ is "
                    + "2(1 + z + 6z² + 7z³ + 2z⁴ + 3z⁵ + z⁶). For every m ≥ 0, "
                    + "d_m = (m + 1)A051176(m + 2) and d_{m+2} = 2A306368(m). Finally, "
                    + "C(m, m + 3) = (−1)^{m+1}A146535(m + 1)/d_m for every m, while the "
                    + "unshifted formula with A146535(m) fails at m = 2. The value follows from "
                    + "the array recurrence. The denominators come from explicit Bézout "
                    + "certificates in each residue class modulo 3. The generating function "
                    + "follows from the resulting order-nine recurrence. The A306368 formula "
                    + "uses Bézout certificates in each residue class modulo 6. This is "
                    + "Corollary 7 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584)."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class FourierFiveThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.";
    private static readonly LibraryNoteRef Qian =
        LibraryNoteRef.Create("D5/L/Entropy/qian2026complementarycorrelations");
    private static readonly LibraryNoteRef Qutrit =
        LibraryNoteRef.Create("D5/L/Quantum/anonymous2026sharpqutritdiscrimination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The combined triangular discrimination of the computational and Fourier measurement outcomes is less than 377/100 for any two complex unit vectors in dimension five.",
        H("The five-dimensional computational and Fourier score threshold"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-fourier-positivefourierscore"),
                DeclarationHandle.Create(Prefix + "positiveFourierScore"), H("The two-basis score"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Qian, Qutrit),
                Blocks(Paragraph(Text("Qian's Eq. (9) gives the score for the two-ray family in Eq. (8). Sum (p−q)²/(p+q) over the computational and normalized positive Fourier outcome tables. A common zero row contributes zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-fourier-positivefourierscore-le-radical"),
                DeclarationHandle.Create(Prefix + "positiveFourierScore_le_radical"), H("The radical upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Qian, Qutrit),
                Blocks(Paragraph(Text("Write A = 1 − √((5 + √5)/10) and E = 1 − √((7 + √5)/10). The Gram compression bounds give the two mask gaps, so every pair of unit vectors satisfies S ≤ 4 − 8E + 8E²/A. Simultaneous conjugation transports the inverse Fourier coordinates to the positive Fourier convention."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-fourier-positivefourierscore-lt-377-div-100"),
                DeclarationHandle.Create(Prefix + "positiveFourierScore_lt_377_div_100"), H("Qian §11(3), the strict threshold"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Qian, Qutrit),
                Blocks(Paragraph(Text("The radical bound gives D ≥ 53682/933125 > 23/400 for the harmonic deficit and S = 4 − 4D. Thus S < 377/100 for every pair of unit vectors. The orthonormal pairs in Qian §11(3) meet these hypotheses."))), DescribeRole.Theorem),
            Paragraph(Text("Qian Theorem 6.14 exhibits an orthonormal pair with S = (14 + 2√5)/5. "
                + "Qian's witness supplies an attained lower bound on the maximum. The sharp maximum remains open. "
                + "The separately deposited qutrit certificate at Zenodo DOI 10.5281/zenodo.23933731 establishes the sharp dimension-three bound and leaves the dimension-five upper bound open."))),
        []));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class SharpBornDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn.";
    private static readonly LibraryNoteRef Qian =
        LibraryNoteRef.Create("D5/L/Entropy/qian2026complementarycorrelations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact maximum of the dimension-five computational and Fourier two-ray score is (14 + 2√5)/5, attained by Qian's orthonormal pair.",
        H("The sharp five-dimensional two-basis score"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-born-inverse"),
                DeclarationHandle.Create(Prefix + "fiveScore_le_sharp"), H("Sharp upper bound for the Born laws"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Qian),
                Blocks(Paragraph(Text("For arbitrary complex unit vectors x and y, sum (p−q)²/(p+q) over the computational and inverse Fourier Born outcome tables, taking a common zero row to contribute zero. The score is at most (14 + 2√5)/5. At or above the proposed cutoff every compatible sign mask is a critical balanced mask. Affine covariance reduces it to centered geometry. The weighted residual separates into reflection-even and odd terms, and the certified estimates absorb the overlap mismatch within the joint Rayleigh deficit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-born-positive"),
                DeclarationHandle.Create(Prefix + "positiveFourierScore_le_sharp"), H("Sharp upper bound in Qian's convention"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Qian),
                Blocks(Paragraph(Text("Simultaneous complex conjugation preserves the norm and transports the inverse Fourier probabilities to the positive normalized Fourier convention of Eq. (9). The upper bound thus holds for all unit pairs, including Qian's orthonormal family."))), DescribeRole.Theorem),
            Paragraph(Text("Qian's Theorem 6.14 and Eqs. (33)–(36) give an orthonormal pair attaining (14 + 2√5)/5. The upper bound together with that previously proved attainment identifies the same maximum for arbitrary unit pairs and for orthonormal pairs."))),
        []));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ThreeDistinguishabilityRealCompressionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/ThreeDistinguishabilityRealCompression";
    private static readonly LibraryNoteRef JointNumericalRange =
        LibraryNoteRef.Create("D5/L/HilbertOperators/lipoon2000jointnumericalrange");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A density supported in the complement of a conjugate pair has a unit vector with the same diagonal.",
        H("Pure replacement in a real complementary plane"),
        Blocks(Describe.Lean(
            DescribeId.Create("pure-replacement-for-conjugate-pair"),
            DeclarationHandle.Create(Module + ".pure_replacement_for_conjugate_pair"),
            H("A diagonal-preserving unit vector"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(JointNumericalRange),
            Blocks(
                Paragraph(Text(
                    "For an orthogonal unit pair z and its conjugate, √2 Re z and √2 Im z form a real "
                    + "orthonormal pair. Let C be a real orthonormal basis matrix for their "
                    + "complement. A positive density B annihilating the pair is supported on the "
                    + "complexification of this plane, so B = C(CᵀBC)Cᵀ.")),
                Paragraph(Text(
                    "Taking the entrywise real part of the compression gives a real symmetric "
                    + "positive matrix T because its quadratic forms on real vectors agree with "
                    + "those of the positive compression. The same operation preserves trace one "
                    + "and the diagonal after lifting through the real matrix C. Diagonalize T with "
                    + "eigenvalues λ, μ ≥ 0 and λ+μ = 1, and lift the unit real eigenvectors to c,e. "
                    + "The complex unit vector √λ c + i√μ e lies in the same plane. The cross term "
                    + "vanishes in each squared modulus, giving λcᵢ²+μeᵢ² = Bᵢᵢ.")),
                Paragraph(Text(
                    "Li and Poon’s Theorem 3.1 gives convexity of the first joint numerical range "
                    + "for measurements in a real symmetric 2 × 2 span. Each effect CᵀEᵢᵢC belongs "
                    + "to that span. Their Theorem 1.2 then gives a rank-one projection with the "
                    + "same four expectations. The Lean construction produces the vector directly "
                    + "from the two real eigenvectors."))),
            DescribeRole.Theorem))));
}

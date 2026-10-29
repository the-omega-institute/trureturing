using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalSourcePairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalSourcePairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal original integer-source complex-bilinear pairing obtained by frequency retuning of the existing signed polynomial Wick supplier.",
        H("Original Integer-Source Bilinear Pairing"),
        Blocks(
            Paragraph(Text("The oscillator carrier remains exactly MvPolynomial (Fin D.rank x Nat) Complex and the charge carrier remains the finite-support Finsupp carrier. integerScale k=(k+1)/(k+1/2) is nonzero and defines an algebra equivalence retune on the same polynomial ring. integerWick is the existing signed Wick form applied to retune in its first slot.")),
            Paragraph(Text("The retained bridge proves integer creation and lowering transposes, symmetry, vacuum normalization, charge isolation and both-sided nondegeneracy. The determinant-unit premise is used only by the inherited Wick nondegeneracy theorem. Rank zero and indefinite integral symmetric even Gram data remain in scope.")),
            Paragraph(Text("All-source wordField BPZ induction, charged-generator transpose, theta isometry, energy orthogonality, mixed Jacobi and translation, crossing, fusion, string consistency and AdS/CFT conclusions are outside this closed unit.")),
            Node("integerScale", "Integer frequency retuning", "The scalar sends the supplier frequency k+1/2 to the required integer contraction k+1.", DescribeRole.Definition),
            Node("retune", "Same-ring oscillator equivalence", "The diagonal substitution equivalence fixes scalars and sends X(i,k) to integerScale k times X(i,k), with an actual inverse.", DescribeRole.Definition),
            Node("integerWick", "Retuned signed Wick form", "The complex-bilinear form is the existing SignedOscillatorWick.wick after retuning the first oscillator slot.", DescribeRole.Definition),
            Node("integerWick_creation", "Integer creation transpose", "Multiplication by X(i,k) in the first slot transposes to -(k+1) times the actual Gram-weighted annihilation in the second slot.", DescribeRole.Theorem),
            Node("integerWick_lowering", "Integer lowering transpose", "The reverse identity is proved using the actual inverse retuning and the supplier lowering theorem.", DescribeRole.Theorem),
            Node("integerWick_symmetric", "Oscillator symmetry", "The retuned oscillator form is symmetric by induction from its creation and lowering bridges.", DescribeRole.Theorem),
            Node("sourcePairing", "Finite opposite-charge lift", "The form sums integerWick over the existing finite charge support and pairs charge a with charge -a.", DescribeRole.Definition),
            Node("sourcePairing_vacuum", "Vacuum normalization", "The literal vacuum has pairing one, including the empty-rank case.", DescribeRole.Theorem),
            Node("sourcePairing_symmetric", "Carrier symmetry", "Finite-support induction lifts oscillator symmetry to the literal Carrier.", DescribeRole.Theorem),
            Node("sourcePairing_nondegenerate", "Two-sided carrier nondegeneracy", "The opposite-charge single-sector witnesses and inherited Wick nondegeneracy prove both kernels vanish under IsUnit D.G.det.", DescribeRole.Theorem)
        ),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("original-source-pairing-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

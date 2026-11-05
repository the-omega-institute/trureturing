using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaOddParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaOddParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual integral Euler quotient has an all-index odd four-dissection.",
        H("CubicThetaOddParity"), Blocks(
            Paragraph(Text("The affine correspondence on complete integer core fibres is consumed by the exact Euler quotient. The integral series is mapped to the existing rational quotient through a proved unit-inverse compatibility.")),
            Node("0", "core_exponent_mod_four_one", "The core exponent is one modulo four exactly when the first coordinate is odd and the second is even.", DescribeRole.Theorem),
            Node("1", "core_exponent_mod_four_ne_three", "No complete core fibre has exponent three modulo four.", DescribeRole.Theorem),
            Node("2", "coreOddEquiv", "The affine map from exponent n to exponent 4*n+1 is a complete fibre equivalence.", DescribeRole.Definition),
            Node("3", "core_product_coeff_mod_four", "The exact rational Euler quotient has the two claimed coefficient identities by the lattice correspondence.", DescribeRole.Theorem),
            Node("4", "integralT", "The integral quotient uses the actual integral pentagonal Euler products and the constant-term-one inverse.", DescribeRole.Definition),
            Node("5", "integralT_map", "The integral quotient maps to the exact rational quotient, including inverse compatibility.", DescribeRole.Theorem),
            Node("6", "integralT_coeff_mod_four", "Every coefficient at 4*n+1 equals the coefficient at n, and every coefficient at 4*n+3 is zero.", DescribeRole.Theorem),
            Paragraph(Text("This is a consumed parity sublemma for the active designated-six-tuple implementation. It does not settle the complete divisibility event and carries no independent novelty or priority claim."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-odd-parity-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

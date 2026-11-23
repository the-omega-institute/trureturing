using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class NativeOddTwistedIntertwinerDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual odd lattice field reverses twisted parity and satisfies finite mixed Borcherds identities.",
        H("The Native Odd Twisted Field"),
        Blocks(
            Paragraph(Text("For lattice data D with unit Gram determinant, the source is the negative eigenspace "
                + "of the lattice involution. The input is the actual twisted space of parity s, and the output "
                + "has parity !s.")),
            Entry("native-odd-twisted-field", "field", "The parity-changing Hahn field",
                "Restrict the corrected lattice coefficients to the stated twisted parities and assemble them "
                + "as a linear field with integer exponents in the doubled coordinate.",
                DescribeRole.Definition),
            Entry("native-odd-twisted-field-coeff", "field_coeff", "Coefficients on the actual tensor",
                "For each signed doubled exponent, the underlying tensor of the typed coefficient is the "
                + "original corrected-field coefficient applied to the underlying input tensor."),
            Entry("native-odd-twisted-field-even-zero", "field_even_zero", "Vanishing at even doubled exponents",
                "Every coefficient at an even doubled exponent vanishes on both input parities."),
            Entry("native-odd-twisted-modes", "J", "The physical half-integer modes",
                "For an integer n, take the field coefficient at doubled exponent -2n-3. This gives "
                + "the bilinear operator with physical mode n+1/2.",
                DescribeRole.Definition),
            Entry("native-odd-twisted-truncation", "J_truncation", "Pointwise lower truncation",
                "For each odd source and input tensor, all modes vanish for sufficiently large integer labels n."),
            Entry("native-odd-twisted-borcherds", "J_borcherds", "Finite mixed Borcherds identity",
                "For a fixed state a, an odd state b, a twisted input v, and integers p, q, r, the iterate "
                + "uses J(p+q-i) on the odd-source product a_(r+i)b with weight binom(p,i). The first product "
                + "applies the fixed mode p+r-i on the output parity to J(q+i)(b)v. The second product "
                + "applies J(q+r-i)(b) after the fixed mode p+i on the input parity, with the additional sign "
                + "epsilon(r). Both products carry the weight (-1)^i binom(r,i). All three families have "
                + "finite support over i >= 0, and the iterate sum equals the first product sum minus the second."),
            Entry("native-odd-twisted-mode-derivative", "J_derivative", "Translation of a physical mode",
                "Replacing the odd source by its lattice translate changes the coefficient at label n "
                + "to -(n+1/2) times the coefficient at label n-1."),
            Entry("native-odd-twisted-field-derivative", "field_derivative", "Iterated field differentiation",
                "After k translations of the source, the coefficient at doubled exponent e equals the original "
                + "coefficient at e+2k times the product of (e+2j)/2 for j from 1 through k."),
            Entry("native-odd-twisted-grade", "J_grade", "Actual output grading",
                "A source of lattice grade h acting at label n on an input of doubled grade M lands in doubled "
                + "grade N whenever N is nonnegative and N = M+2h-2n-3."),
            Entry("native-odd-twisted-negative-grade", "J_negative_grade_zero", "Negative output grade",
                "The mode vanishes when the signed doubled output index M+2h-2n-3 is strictly negative."),
            Entry("native-odd-twisted-ground-return", "J_ground_return", "Ground return with the Gram coefficient",
                "On an arbitrary even ground tensor, creation in direction j at physical mode -1/2 followed "
                + "by annihilation in direction i at physical mode 1/2 returns G(i,j)/2 times the input."),
            Entry("native-odd-twisted-leech-normalization", "leech_normalization", "Explicit Leech ground normalization",
                "On the specified weight-3/2 Leech ground vector, the mode -1/2 in direction i gives the actual "
                + "nonzero one-oscillator vector of doubled grade 1. The reverse mode 1/2 in the same direction "
                + "returns G(i,i)/2 times the ground vector, and the return is nonzero."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

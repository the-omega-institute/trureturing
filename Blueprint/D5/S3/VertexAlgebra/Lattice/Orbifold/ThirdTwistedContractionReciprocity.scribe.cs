using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedContractionReciprocityDocument : IScribeDocumentDefinition
{
    private const string Orbifold = "D5/S3/VertexAlgebra/Lattice/Orbifold/";
    private const string Prefix = Orbifold + "ThirdTwistedContractionReciprocity.";
    private static readonly LibraryNoteRef TwistedLattice =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational contraction reciprocity and cancellation by the order-three charge multiplier.",
        H("Order-Three Rational Contraction Reciprocity"),
        Blocks(
            Paragraph(Text("Let D be the native even integral lattice with pairing ⟨a,b⟩ and let g be "
                + "an additive equivalence of its charges. The rational contraction uses the cover "
                + "ratio t = (w/z)^(1/3) from Bakalov–Kac, arXiv:math/0402315v3, Lemma 4.2, equation (4.34). "
                + "Write N = 1 + g + g² for the integral orbit norm.")),
            Describe.Lean(
                DescribeId.Create("third-twisted-rational-contraction"),
                DeclarationHandle.Create(Prefix + "rationalContraction"),
                H("Rational contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(TwistedLattice),
                Blocks(Paragraph(Text("For a complex unit u, multiply the three binomials 1 − uʲt "
                    + "to their integer powers ⟨gʲa,b⟩ in the complex rational-function field."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-reciprocity-phase"),
                DeclarationHandle.Create(Prefix + "reciprocityPhase"),
                H("Reciprocity phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("The phase is the product of the complex units −uʲ raised to "
                    + "the respective integer powers ⟨gʲa,b⟩."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-rational-reciprocity"),
                DeclarationHandle.Create(Prefix + "rationalContraction_reciprocity"),
                H("Reciprocity under charge and ratio reversal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("Assume g is a pairing isometry, g³ = 1, u³ = 1, and t is nonzero. "
                    + "Inverting each binomial gives a factor of t times its leading coefficient. "
                    + "The factors of t combine with exponent ⟨Na,b⟩. Symmetry and isometry identify "
                    + "the product with inverted root parameter with the product on the reversed charges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-rational-expansion"),
                DeclarationHandle.Create(Prefix + "rationalContraction_X_expansion"),
                H("Laurent expansion at the indeterminate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("At the indeterminate X, the Laurent expansion is the product "
                    + "of the power-series binomial units with the same integer powers. This is the "
                    + "product appearing in "), Ref(Orbifold + "ThirdTwistedContraction.scalar_contraction"),
                    Text(" with complex parameter u. The expansion holds for every complex unit u."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-cocycle-phase"),
                DeclarationHandle.Create(Prefix + "c_mul_reciprocityPhase"),
                H("Cancellation by the charge multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("For ζ = exp(2πi/3), the phase multiplies the Bakalov–Kac "
                    + "coefficient "), Ref(Orbifold + "ThirdTwistedChargeCocycle.c"),
                    Text(" on (a,b) to give its value on (b,a). The two nontrivial cyclotomic "
                    + "factors of B exchange, and the binomial sign at j = 0 cancels the sign from ε."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-weighted-rational-reciprocity"),
                DeclarationHandle.Create(Prefix + "c_mul_rationalContraction_reciprocity"),
                H("Reciprocity of the cocycle-weighted contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedLattice),
                Blocks(Paragraph(Text("At the Bakalov–Kac root and nonzero t, the cocycle-weighted "
                    + "contraction equals the weighted contraction on (b,a) at t⁻¹ times t raised to "
                    + "⟨Na,b⟩. The phase cancellation is an identity of rational functions."))),
                DescribeRole.Theorem))));
}

using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TransverseMetric;

internal sealed class LorentzianSignatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lorentzian inertia and native transverse positivity",
        H("Lorentzian inertia and native transverse positivity"),
        Blocks(
            Paragraph(Text("A real invertible null-pair frame splits the original ambient quadratic form into a hyperbolic plane and the actual transverse row Gram. The argument applies to every supported rank and does not require the frame to be orthonormal, its entries to be integral, or the ambient Gram to be positive definite. The ambient signature is the actual positive-minus-negative inertia count. The resulting strict positivity statements concern the original algebraic transverse polynomial image and its native degree-one tensor states. Physical-image equivalence, quotient positivity, the neutral radical, a full no-ghost theorem and the string or AdS/CFT bridge are separate conclusions not supplied here.")),
            Describe.Lean(
                DescribeId.Create("lorentzian-axisequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.axisEquiv"),
                H("Null axes and the transverse coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two distinct axes partition all ambient coordinates into the two null coordinates and the literal transverse subtype."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lorentzian-transverse-card"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverse_card"),
                H("Dimension of the transverse sector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The partition proves that the transverse cardinality plus two is exactly the ambient rank, including rank two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lorentzian-coordinateequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.coordinateEquiv"),
                H("The actual coordinate splitting"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward map evaluates the two null coordinates and restricts to the transverse coordinates. Its inverse inserts exactly these coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lorentzian-realframe"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.realFrame"),
                H("The real frame matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every matrix entry is the real part of the original complex frame entry. Star-fixed entries recover the original frame without changing its normalization."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lorentzian-ambient-equivalent-split"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.ambient_equivalent_split"),
                H("Hyperbolic plane and the literal transverse Gram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supplied frame inverses give a real invertible change of basis. The two dual-row laws fix the hyperbolic block to two times the product of the null coordinates and annihilate the cross terms with every transverse coordinate. No orthonormality or diagonal transverse matrix is assumed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lorentzian-transversegram-posdef"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.transverseGram_posDef"),
                H("Lorentzian inertia implies transverse positivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hyperbolic block has signature zero. Signature additivity and invariance therefore give transverse signature equal to its dimension. The maximal positive subspace then has full dimension and is the whole transverse space. The mostly-plus convention is positive-minus-negative signature equal to ambient rank minus two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lorentzian-nativepolynomial-positive-of-lorentzian"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.nativePolynomial_positive_of_lorentzian"),
                H("Strict native polynomial positivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proved Gram positivity is inserted into the original finite-support complex polynomial Fock theorem. Every nonzero native transverse polynomial has a strictly positive real norm and zero imaginary part, without a fixed energy or occupation cutoff."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lorentzian-native-degree-one-negative-c0-positive-of-lorentzian"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TransverseMetric/LorentzianSignature.native_degree_one_negative_C0_positive_of_lorentzian"),
                H("The original degree-one negative right-C0 pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same Gram theorem supplies the original native State and J-eigenvalue-one theorem with both Gram inverse laws and both frame inverse laws. The sign is exactly the negative of the original right-C0 Hermitian pairing; neither a physical cohomology quotient nor its positivity is inferred."))), DescribeRole.Theorem))));
}

using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeCreationTranslationAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native creation and finite translation coefficient adjoints",
        ArtifactId.Parse("D5/S3/VertexAlgebra/LatticeCreationTranslationAdjoint"),
        "D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint",
        Blocks(
            Paragraph(Text("The carrier is the existing polynomial oscillator over all pairs of a lattice axis and a natural frequency. Charges, vertex indices and coefficient indices remain unrestricted integers. The integral Gram form may be singular, indefinite or of rank zero. No inverse matrix, positivity, invariant-form axiom, exponential adjoint assumption or finite occupation cutoff is used.")),
            Paragraph(Text("The actual Gram annihilator is frequency times the native weighted partial derivative. Its all-integer creation-coefficient recurrence follows directly from the existing annihilation_creation supplier, cancelling the nonzero frequency factor. Positive creation indices have zero constant coefficient by the existing actual_creation_coefficient_transport weighted-homogeneity theorem. Index zero is extracted directly from LatticeFiniteNegativeGeneration.actual_negative_single on the vacuum, rather than reproving its exponential constant term. Negative indices vanish by definition.")),
            Paragraph(Text("translationCoeff uses the coefficient of the actual translatedPolynomial for nonnegative integer indices and zero otherwise. The coefficient adjoint is proved by induction on the entire polynomial in the right slot, generalizing both the left polynomial and the integer coefficient index. The reverse creator adjoint, actual derivation product rule and creation recurrence supply the generator step. The translated variable has the original bilinear coefficient and the frequency power; no formal infinite operator sum is interchanged.")),
            Paragraph(Text("This is standard lattice Fock contravariance, with zero literature novelty asserted. Kac, Frenkel-Lepowsky-Meurman and Borcherds provide the existing classical context. A charged full-state invariant form, Sugawara L1 local nilpotence, descendant opposite modes, the original ghost and BRST adjoints, quotient isometry, physical no-ghost, moonshine, full string theory and AdS/CFT remain separate obligations.")),
            Paragraph(Text("The consumed creation_constant, translation_polynomial_creator and form_integral_smul_left suppliers retain their original proofs in this owning module and are publicly addressable for direct reuse by LatticeConvolutionFockAdjoint. Source visibility repair carries zero new mathematical novelty.")),
            Describe.Lean(
                DescribeId.Create("latticecreationtranslationadjoint-creation-constant"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeCreationTranslationAdjoint.creation_constant"),
                H("Original creation constant coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing all-integer constant-coefficient supplier is reused without altering its hypotheses or proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticecreationtranslationadjoint-translation-polynomial-creator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeCreationTranslationAdjoint.translation_polynomial_creator"),
                H("Original translated creator polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual translatedPolynomial generator identity retains its original integral bilinear coefficient and frequency power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticecreationtranslationadjoint-form-integral-smul-left"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeCreationTranslationAdjoint.form_integral_smul_left"),
                H("Original integral scalar identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing integral scalar identity for the original conjugate-linear left slot is reused directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticecreationtranslationadjoint-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeCreationTranslationAdjoint.creation_translation_adjoint"),
                H("Every integer creation coefficient is adjoint to finite opposite-charge translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integral symmetric even-diagonal lattice, every charge, every integer t and every two finite oscillator polynomials p and q, fockForm(creationCoeff(alpha,t) times p,q) equals fockForm(p,translationCoeff(-alpha,t,q)). Negative integer coefficients vanish on both sides by the actual definitions."))),
                DescribeRole.Theorem))));
}

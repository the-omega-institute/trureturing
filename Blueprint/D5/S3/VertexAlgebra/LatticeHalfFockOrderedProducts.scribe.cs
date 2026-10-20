using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOrderedProductsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native half-Fock oscillator coefficient composition equals its supported contraction expansion.",
        H("Native Ordered Half-Fock Products"),
        Blocks(
            Paragraph(Text("Fix arbitrary lattice data D, charges left and right, integer indices first "
                + "and second, and an oscillator polynomial p. Normalize each oscillatorCoefficient "
                + "index by subtracting chargeNorm of its own charge. The ordered expansion uses "
                + "halfContraction coefficients and commonKernel at first+d,second-d. "
                + "Rectangular lower bounds give finite support in d separately for each p.")),
            Describe.Lean(
                DescribeId.Create("half-fock-native-ordered-product"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts.native_ordered_product"),
                H("The actual oscillator composition is the finite ordered-diagonal sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("oscillatorCoefficient D left (first-chargeNorm D left) applied to "
                    + "oscillatorCoefficient D right (second-chargeNorm D right) p equals the finsum "
                    + "over natural d of halfContraction.coeff(d) smul "
                    + "commonKernel D left right (first+d) (second-d) p. No positivity, determinant-unit, "
                    + "homogeneity, nonzero-charge or bounded-index assumption is added."))), DescribeRole.Theorem),
            Paragraph(Text("The constant case converts the actual oscillator sum to finite polynomial "
                + "convolution and uses half_creation_coefficient_transport. Polynomial induction then "
                + "handles addition and creators. On the creator branch, both actual coefficient "
                + "recurrences are reused through oscillator_coefficient_X_mul, whose original private "
                + "proof remains in ChargedTensorCoefficients. The common-kernel creator recurrence "
                + "and finite-sum algebra identify the three shifted induction terms.")),
            Paragraph(Text("The private orderedExpansion is linear because addition and scalar "
                + "multiplication are justified by finite supports after fixing each polynomial. "
                + "This does not claim a uniformly finite sum in the endomorphism space. "
                + "PhysicalLocality consumes the theorem in its pure tensor product expansion; "
                + "ground actions and cocycle exchange are supplied there separately.")),
            Paragraph(Text("The half-Fock construction and transport APIs are inherited; this exact "
                + "polynomial induction and finite coefficient composition are repository-derived. "
                + "FLM is background attribution with no full-text inspection or literature novelty "
                + "claim here. The theorem establishes an algebraic ordered product, without "
                + "asserting analytic convergence, all-source locality or twisted Jacobi.")))));
}

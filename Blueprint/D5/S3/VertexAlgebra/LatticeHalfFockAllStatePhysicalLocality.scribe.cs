using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockAllStatePhysicalLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical corrected field is local at one doubled-shift order for every pair of finite-charge sources.",
        H("All-source Physical Locality"),
        Blocks(
            Paragraph(Text("For arbitrary integral symmetric even lattice data D, a determinant unit hu, "
                + "sources first and second in the existing Carrier D, every signed integer exponent pair and "
                + "every ActualTensor D hu state, one natural order is selected before the exponents and state. "
                + "The displayed binomial sum of corrected-field coefficients at the even shifts "
                + "2*(order-offset) and 2*offset is zero.")),
            Paragraph(Text("The proof uses the existing charged coefficient locality supplier, direct signed "
                + "physical slices and jets, canonical singleton insertion, uniform-shift Dong locality for "
                + "repeated words, and the unchanged finite Corr/charge/basis expansion of correctedField. "
                + "Finite support is used pointwise after fixing the actual tensor input; no positivity, "
                + "homogeneity, source-product or extra locality premise is introduced.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockallstatephysicallocality-corrected-field"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality"),
                H("Exact unrestricted all-source physical locality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The witness order depends only on the two fixed sources and lattice data. "
                    + "It is chosen before all signed exponents and target vectors. The cover grid is the "
                    + "commutator of the two physical slices at shifts -E-2 and -F-2; finite linear closure "
                    + "over the actual charge, correction-shift and repeated monomial supports gives the "
                    + "corrected-field coefficient identity."))),
                DescribeRole.Theorem),
            Paragraph(Text("This algebraic result leaves source-product compatibility, twisted Jacobi, analytic "
                + "CFT completion, fusion, string theory and AdS/CFT as separate obligations.")))));
}

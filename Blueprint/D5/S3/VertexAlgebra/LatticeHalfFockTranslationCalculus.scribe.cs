using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTranslationCalculusDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Physical Differentiation.",
        H("Native Physical Differentiation"),
        Blocks(
            Paragraph(Text("Physical differentiation uses z=x^2. Its integer-cover coefficient at E is (E+2)/2 times the original coefficient at E+2, not the bare cover derivative. The field constructor retains the original ActualTensor carrier and proves its lower truncation from the input field's support.")),
            Describe.Lean(
                DescribeId.Create("latticehalffocktranslationcalculus-normal-insertion-physical-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalInsertion_physical_derivative"),
                H("Physical derivative of native normal insertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every native field and every oscillator index (i,k), physical differentiation of its normal insertion equals (k+1) times insertion of (i,k+1), plus insertion of (i,k) into the physically differentiated field. The proof differentiates the actual jetScalar factorial product. Each negative and positive summand satisfies the product law before summation; the existing separate statewise finite-support theorems justify both sum interchanges. No assumed translation, Jacobi, positive signature, rank or occupation restriction is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktranslationcalculus-normal-sequence-physical-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus.normalSequence_physical_derivative"),
                H("Physical product law for every finite normal word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every finite word, including empty words and repeated indices, the derivative is the finite sum over labelled deletions of (k+1) times insertion of (i,k+1) into the remaining word, plus the unchanged word acting on the differentiated base field. Linearity of the original normalInsertion is proved using the unfiltered singleton flatTerm expansion and its genuine finite support, then the original insertion commutation permutes the replacement factor. No nested normal tail order is used to bound individual flattened summands."))),
                DescribeRole.Theorem),
            Paragraph(Text("The complete original all-state identity is addressed by LatticeHalfFockOriginalTranslation, which joins the actual charged differentiation and Corr recurrence. This insertion product law alone does not establish differentiation of the charged creation exponential, its finite translated polynomial, the chargeScalar prefactor or its actual ground operator. Locality and this product law alone do not prove twisted Jacobi or the full moonshine, string or AdS/CFT goals.")),
            Paragraph(Text("The Reg mirror proves the full dependent coefficient-readout equivalence for the insertion theorem and records a separate full-telescope word readout obligation. Neither is a declared_validated four-slot registration: enrolled-template variation, sensitivity, observational dependence and source selection still require evidence.")))));
}

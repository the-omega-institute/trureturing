using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedTranslationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Charged Ground Translation.",
        H("Actual Charged Ground Translation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockchargedtranslation-original-ground-translation-physical"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedTranslation.original_ground_translation_physical"),
                H("Literal source translation on actual target ground states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every original charge, integer coefficient and actual twisted ground vector, Ytw of the literal Sugawara source translation of the charged source ground state equals (E+2)/2 times the charged field coefficient at E+2. The proof differentiates the actual halfCreationExponential through its original exponential chain rule, extracts the even logarithmic derivative coefficients and proves a statewise finite creation recurrence for every signed integer degree. It then consumes the original first-descendant mixed iterate, including its charge-dependent minus-one-half correction. The original chargeScalar=2^(-chargeNorm), exponent shift from x^(-chargeNorm), actual groundAction and groundRepresentation remain present. No positivity, signature, rank, occupation or charge restriction is introduced."))),
                DescribeRole.Theorem),
            Paragraph(Text("This endpoint has a charged source ground state and a target ground tensor. Its subsequent all-target extension is separate; it is not the full oscillator-source covariance theorem or twisted Jacobi. The Reg mirror proves the full dependent readout equivalence but does not yet provide declared_validated four-slot source admission. Variation, sensitivity, observational dependence and lawful enrolled-template selection remain obligations. The full moonshine, string and AdS/CFT program remains open.")))));
}

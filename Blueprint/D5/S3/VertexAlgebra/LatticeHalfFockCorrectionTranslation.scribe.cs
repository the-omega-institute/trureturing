using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCorrectionTranslationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite charged correction intertwines sector translation",
        H("Finite charged correction intertwines sector translation"),
        Blocks(
            Paragraph(Text("For every LatticeData D, charge in Charge D and polynomial in Oscillator D, the original finite Corr applied after LatticeSugawaraConformal.sectorTranslation equals the coefficient transport of the correction connection plus the charge-weighted insertion sum. Lattice rank, charge and oscillator degree have no additional restriction. Degenerate, indefinite and rank-zero lattice data remain in scope. This pure correction-algebra identity does not require a unimodularity hypothesis.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockcorrectiontranslation-sector-translation"),
                DeclarationHandle.Create(Prefix + "Corr_sectorTranslation"),
                H("The actual finite correction intertwines sector translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("The connection sends the shift variable t to -t^2 and an ordinary variable indexed by i to its source weight times the successor variable, minus the charge-weighted pair polynomial sum. The right side retains the original singletonPolynomial, pairPolynomial, pairDerivation, insertion and correction coefficients; it is not an assumed compatibility equation.")),
                    Paragraph(Text("correctedSource is the original correctionPolynomial transported back through optionEquivLeft. Cancellation identifies it with the frozen CurrentCorrection.correctionLift. The proof directly consumes correctionLift_X_mul, correctionLift_C and FiniteCorrection.pairDerivation_variable. Only the visibility of the latter two original declarations changes; their statements and proofs are retained.")),
                    Paragraph(Text("The live all-polynomial inference is correctedSource_oscillatorDerivation. Scalar recurrences give the connection commutator with pairDerivation and the derivative of the singleton multiplier. Together they yield the insertion Leibniz law; polynomial induction then intertwines the oscillator derivation with the connection. Adding the actual chargePolynomial contribution and applying optionEquivLeft and shiftCoefficients produces the public endpoint. The correction lift is linear with Wick pair contractions, so multiplicative polynomial evaluation is not a premise of this induction."))),
                DescribeRole.Theorem),
            Paragraph(Text("The owning Reg mirror preserves the full dependent lattice, charge and polynomial telescope, the actual Corr output family and an exact source-equivalence bridge. Its typed realization supplies whole-family variation, sensitivity and observational dependence; continuation is explicitly unknown. The scoped report validates this source-equivalence registration and the registrations for the two exported support lemmas. The open continuation records an unknown residual, not a proof of completeness or inexhaustibility.")),
            Paragraph(Text("The preserved source-only LatticeHalfFockOriginalTranslation.correctedPolynomial_physical consumes Corr_sectorTranslation as a rewrite before correction_operation_identity and normalEvaluation_physical. That downstream source is not restored or certified by this unit. Its unimodularity and charged field obligations are not removed by the absence of such a hypothesis from this pure correction law.")),
            Paragraph(Text("This is a repository derivation in the classical FLM twisted lattice correction calculus, reusing the frozen correction library and pinned Mathlib derivation extensionality, commutator and polynomial induction. No literature novelty is claimed. It is a general symbolic theorem, not a certified finite instance or bounded enumeration; utility is none. Full corrected-field translation, twisted Jacobi, native BPZ integration and the VOA/CFT, anomaly/fusion, string and AdS/CFT programme remain open.")))));
}

using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full charged correction commutes with source partial derivatives",
        H("The full charged correction commutes with source partial derivatives"),
        Blocks(
            Paragraph(Text("LatticeData has arbitrary finite rank and a symmetric integral Gram matrix with even diagonal. Rank zero, degenerate and indefinite forms remain in scope. Every charge, oscillator index, finite oscillator polynomial and natural correction shift retains its original domain; there is no occupation or order cutoff.")),
            Paragraph(Text("The operator is exactly the original Corr. Its correctionWord has the original singletonPolynomial, pairPolynomial and pairDerivation; no neutral substitution or alternative correction map is used.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentcorrection-correctionlift-c"),
                DeclarationHandle.Create(Prefix + "correctionLift_C"),
                H("The correction lift fixes scalar constants"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original constant lemma is public for direct reuse by correctedSource_oscillatorDerivation in CorrectionTranslation. It is consumed support, not additional mathematical content."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentcorrection-occurrences-cons"),
                DeclarationHandle.Create(Prefix + "occurrences_cons"),
                H("Adding one exponent adds one labelled occurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every lattice D, index i and finitely supported natural exponent e, the list i :: occurrences(D,e) permutes occurrences(D,e + single(i,1)). The multiset equality retains repeated occurrences. This enumeration identity supplies the monomial step of correctionLift_X_mul."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentcorrection-lift-x-mul"),
                DeclarationHandle.Create(Prefix + "correctionLift_X_mul"),
                H("Multiplication by a source variable becomes the original insertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every D, charge a, index i and oscillator polynomial p, correctionLift(D,a)(p X_i) equals insertion(D,a,i)(correctionLift(D,a)(p)). The lift uses the monomial basis and the original correctionWord. Polynomial induction reduces multiplication to occurrence insertion, and correctionWord_permutation removes the dependence on occurrence order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentcorrection-lift-partial"),
                DeclarationHandle.Create(Prefix + "correctionLift_partial"),
                H("Source partial derivatives commute with the polynomial correction lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every D, charge a, index i and oscillator polynomial p, partial_(some i)(correctionLift(D,a)(p)) equals correctionLift(D,a)(partial_i(p)). Ordinary source partials annihilate the singleton and pair coefficients, commute with pairDerivation, and differentiate insertion by its retained-variable term plus insertion of the derivative. Polynomial induction then gives the unrestricted lift identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentcorrection-corr-partial"),
                DeclarationHandle.Create(Prefix + "Corr_partial"),
                H("The full charged correction commutes with source partial derivatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The source derivative at any ordinary index commutes coefficientwise through Corr for every charge, polynomial and correction shift. The proof establishes partial_pairDerivation and partial_insertion on the actual correction polynomial, retaining the charged singleton and pair constants, and then passes through optionEquivLeft."))),
                DescribeRole.Theorem),
            Paragraph(Text("The singleton coefficient at source weight one is the actual negative charge pairing divided by two. The pair coefficients retain pairScalar and both halfBinomial factors. They are constants for the source partial derivative, not deleted terms. Passing through optionEquivLeft and extracting each shift coefficient gives Corr_partial. The original frequency-weighted current law still requires the actual charge zero mode.")),
            Paragraph(Text("The five public identities each have a source-bound Contract.Registration with its complete original parameter and state telescope, an exact source-equivalence bridge, a lawful actual readout, a rejected whole-family intervention with variation and sensitivity, and actual observational dependence: correctionLift_C, occurrences_cons, correctionLift_X_mul, correctionLift_partial and Corr_partial. Finite roles impose no finiteness on parameters, states or outputs; whole-family variation retains zero and degenerate fibers. Each registration's unknown continuation records only the unresolved residual.")),
            Paragraph(Text("These are repository derivations of classical twisted lattice correction identities with FLM background, with no literature novelty claim. The next operator step is the original frequency-weighted Corr current identity with its charge zero mode. This unit does not establish arbitrary-ground closed scalar evaluation, native all-state BPZ integration, full twisted Jacobi, or the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives.")))));
}

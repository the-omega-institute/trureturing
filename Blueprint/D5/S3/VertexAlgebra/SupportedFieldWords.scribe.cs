using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class SupportedFieldWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SupportedFieldWords.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual HVertexOperator composition supplies supported ordered words and their finite clearing action.",
        H("Supported actual field words"),
        Blocks(
            Paragraph(Text("For a K-module V and finitely many actual VertexOperator maps, compose operators on the "
                + "given input vector in their displayed order. Carnahan HVertexOperator composition applies "
                + "each prefix operator to the actual suffix coefficient vector. Its lower truncation is "
                + "contextual; no simultaneous truncation bound for all vectors is supplied or required.")),
            Describe.Lean(
                DescribeId.Create("supportedfieldwords-ordered-coeff"),
                DeclarationHandle.Create(Prefix + "ordered_coeff"),
                H("Coefficients of the complete actual word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("The exponent vector records coefficients in the recursively ordered Hahn group. The "
                        + "coefficient at e is the successive mode action with mode index -e_i-1. Scalar evaluation is "
                        + "a linear map applied after that action, with the same operator ordering."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supportedfieldwords-supported-finite-convolution"),
                DeclarationHandle.Create(Prefix + "supported_finite_convolution"),
                H("Finite labelled clearing is Hahn multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("The finite Laurent polynomial acts by the shifts e-b, summed over its actual finite support. "
                        + "Monomial induction and Hahn coefficient multiplication show that this action equals "
                        + "multiplication on a supported word. Polynomial embeddings are injective; uniqueness and "
                        + "rational reconstruction use cancellation only in the supported Hahn field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supportedfieldwords-scalarwordcarrier-actual-coeff"),
                DeclarationHandle.Create(Prefix + "scalarWordCarrier_actual_coeff"),
                H("The native graded-local distribution is the actual coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("For complex graded-local fields D and output selector, word_ofFn identifies the list of "
                        + "actual modes with the complete HVertexOperator composition applied to D.vacuum. "
                        + "ScalarWordCarrier at every integer labelled exponent equals lambda of "
                        + "coefficientDistribution D.field D.vacuum selector.map (List.ofFn sigma). The evaluator is "
                        + "lambda composed with selector.map."))),
                DescribeRole.Theorem),
            Paragraph(Text("The algebraic proofs reuse mathlib Hahn/Laurent support, finite antidiagonal multiplication, "
                + "fraction-field lifts and polynomial partial fractions. LaurentSeries authors are Aaron "
                + "Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio; HahnSeries author is "
                + "Aaron Anderson; partial fractions authors are Kevin Buzzard, Sidharth Hariharan and Aaron "
                + "Liu. These sources carry Apache 2.0 licenses. Actual HVertexOperator and VertexOperator "
                + "composition are by Scott Carnahan, Apache 2.0. The imported FieldNormalProduct supplier "
                + "attributes its support/Hasse adaptation to ScottCarnahan/vertexAlg revision "
                + "4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. The locality LibraryNote association "
                + "is background, not a claim that these new rational proofs are supplied by that paper.")),
            Paragraph(Text("Matsuo and Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide "
                + "residue-product locality and reconstruction background. Their reconstruction requires "
                + "additional creative generators and a common translation operator. Carpi and Codogni, "
                + "arXiv:2605.26972v1, Conjecture 14.4 concerns all weights; Proposition 14.3 treats k<24. The "
                + "corrected coefficient is D(h,j)=j!(2h)_j; the faulty printed Equation 46 is unused here. No "
                + "proof of that conjecture, actual Moonshine/PCT, a fused-state energy law, "
                + "CFT/anomaly/fusion, string theory or AdS/CFT is asserted.")))));
}

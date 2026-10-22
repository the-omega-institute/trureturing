using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockNativeNormalActionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockNativeNormalActions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native normal actions on the unrestricted original algebraic tensor carrier.",
        H("Native Normal Actions And Finite Leibniz Contractions"), Blocks(
            Paragraph(Text("D is the original unrestricted integral lattice datum, hu is the original "
                + "IsUnit determinant witness, and the target is the original oscillator tensor the actual "
                + "chosen ground representation. All integral current modes, all oscillator levels and all "
                + "repeated labels are retained. There is no positivity, occupation restriction, finite-energy "
                + "replacement, inverse of the distinguished shift variable or assumed operator comparison. "
                + "The constructions are project-native algebraic consequences of the existing current "
                + "and Fock-normal field suppliers; no new literature theorem or originality is claimed.")),
            Describe.Lean(DescribeId.Create("actual-positive-word-leibniz"),
                DeclarationHandle.Create(Prefix + "actual_positive_word_leibniz"),
                H("Actual Positive-Current Word Leibniz Expansion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every signed ModeTuple, oscillator polynomial p and arbitrary actual "
                        + "tensor v, the original rightAction applied to polynomial multiplication p times v "
                        + "is the finite sum over every ordered Leibniz split of the positive currents. "
                        + "Each derivative is exactly jetScalar(order,mode) times frequency(mode) times the "
                        + "original Gram-weighted annihilationDerivation at mode.toNat. The chronological "
                        + "operator order is the original rightAction order. Splits preserve occurrence "
                        + "multiplicity; negative currents are not inserted into the derivative list. "
                        + "The iterated product rule is proved, not assumed, and tensor induction handles "
                        + "all finite algebraic superpositions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-normal-word-finite-action"),
                DeclarationHandle.Create(Prefix + "actual_normal_word_finite_action"),
                H("Finite Original Normal-Word Action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every original charge, word, integer coefficient and actual tensor, there is a "
                    + "finite set of signed mode tuples giving the exact original normalWord action. "
                    + "The summand is normalSplitCoefficient, a finite list sum of chargeScalar times the "
                    + "tensor map of the negative-current creation polynomial, oscillatorCoefficient at "
                    + "exponent+2*modeSum+jetShift, and the two ordered positive derivative words. "
                    + "The original groundAction is unchanged. The negative creation variable is exactly "
                    + "X(colour,(-mode-1).toNat) with its jetScalar. Finiteness comes from the existing "
                    + "pointwise flatTerm support theorem, not a carrier cutoff. It bounds the aggregated "
                    + "split coefficient; this statement does not assert global termwise support before "
                    + "summing the Leibniz splits."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-native-correction-finite-action"),
                DeclarationHandle.Create(Prefix + "actual_native_correction_finite_action"),
                H("Actual Native Correction Evaluation On Every Tensor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every full CorrectionPolynomial, the actual "
                        + "nativeCorrectionEvaluation coefficient on p times an arbitrary actual tensor is "
                        + "a finite sum over the original shiftCoefficients support, each oscillator "
                        + "polynomial's full monomial support, and a state-dependent finite set of signed "
                        + "mode tuples. The physical coefficient is exponent+2*shift, followed by the exact "
                        + "flat shift 2*modeSum+jetShift. Setting p=1 covers an arbitrary original tensor "
                        + "without restricting its oscillator support or ground component. The source "
                        + "coefficients are obtained by the original optionEquivLeft and shiftCoefficients; "
                        + "the distinguished variable is never inverted or specialized.")),
                    Paragraph(Text("This is an actual operator-side finite-action expansion, not the "
                        + "complete Lambda/commonKernel comparison. The full creation, annihilation and "
                        + "independent-sheet symbol factors remain their existing suppliers. Relating the "
                        + "native split derivative terms to those symbols with joint coefficient interchange, "
                        + "combining the checked scalar ratio with the original choose factors and single "
                        + "cocycle, and proving the genuine recurrence, both initial values and both "
                        + "unchanged all-j endpoints remain open. This module does not complete the full "
                        + "VOA/CFT/string or AdS programme."))), DescribeRole.Theorem))));
}

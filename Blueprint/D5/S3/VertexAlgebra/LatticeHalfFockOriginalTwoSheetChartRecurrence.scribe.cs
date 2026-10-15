using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOriginalTwoSheetChartRecurrenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Cleared Charged Two-Sheet Charts.",
        H("Native Cleared Charged Two-Sheet Charts"),
        Blocks(
            Paragraph(Text("NativeLattice packages exactly the original integral lattice and its original determinant-unit witness. Every charged coefficient, common kernel and target tensor still uses those literal components. The package carries no chart identity, iterate law, positivity, rank restriction or inverse Gram matrix.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockoriginaltwosheetchartrecurrence-cleared-diagonal-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOriginalTwoSheetChartRecurrence.cleared_diagonal_support"),
                H("Finite diagonal support of literal cleared charged products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every original lattice, determinant-unit witness, two signed charges, integer total exponent and arbitrary actual target tensor, the literal cleared ordered coefficient has finite diagonal support. Clearing is the finite alternating binomial sum of native chargedField coefficients with doubled cover shifts and order equal to the absolute signed pairing. No positivity, inverse Gram matrix, fixed rank, energy restriction or occupation cutoff is used.")),
                    Paragraph(Text("The proof first identifies that alternating sum with the existing physical difference iterate on actual pure tensors, using the original coefficient normalization and actual ground operator composition. Native clearing then reduces it to the existing cleared polynomial, whose degree is bounded by twice the clearing order. Tensor-product extensionality identifies the resulting finite tensor common-kernel sum. The original tensor common-kernel rectangular lower bounds force every cleared nonzero diagonal coefficient into a finite integer interval. This proves support before any chart weighting or sum interchange.")),
                    Paragraph(Text("The literal localPlus and localMinus maps use Ring.choose(e/2,r) and the minus-sheet integer power (-1)^e on that finite diagonal. Their linearity consumes the proved support. The minus-sheet construction consumes the original charged coordinate-monodromy theorem and the even doubled clearing shifts; it does not introduce an independent global sign or replace the original field. The owning Reg mirror supplies the original theorem reconstruction, actual-positive law, whole-family variation, sensitivity and genuine target-state observational dependence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockoriginaltwosheetchartrecurrence-local-charts-below-start"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOriginalTwoSheetChartRecurrence.local_charts_below_start"),
                H("Both literal charts vanish below their exact signed starting orders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every chart order, integer total exponent and arbitrary actual target tensor, localPlus vanishes when the order is below (N+g).toNat, and localMinus vanishes when it is below (N-g).toNat. Here g is the signed original bilinear pairing and N is its absolute value. The same unrestricted lattice and native determinant-unit witness are retained.")),
                    Paragraph(Text("The proof keeps the actual common-kernel coefficients on a fixed diagonal. Its rectangular bounds prove finite support separately for every shifted summand before interchanging the finite polynomial sum and the diagonal finsum. An integer translation reindexes each summand onto that common diagonal. The remaining scalar weight is the finite coefficient of the original cleared polynomial evaluated at the formal binomial series with exponent minus one half, multiplied by the integer-dependent binomial series.")),
                    Paragraph(Text("That cleared polynomial has the factor (1-R) to the power twice g.toNat. Since R has constant coefficient one, the factor has formal order at least twice g.toNat. Every lower coefficient is therefore zero. The identity (N+g).toNat = 2*g.toNat gives the plus starting order without a sign hypothesis. The minus statement consumes the original charged coordinate monodromy and replaces the first charge by its actual negative; it yields (N-g).toNat = 2*(-g).toNat, with no extra sign or cocycle. The polynomial coefficient argument uses only finite sums and formal series, not convergence or an infinite chart substitution.")),
                    Paragraph(Text("The Reg realization reads both actual chart values. Its rejected family is the unmodified target pair; a genuine even unimodular hyperbolic lattice supplies a nonzero target at a positive starting order. A rank-zero identity-field witness separately establishes actual state dependence. These witnesses test the readout and do not restrict the theorem domain."))),
                DescribeRole.Theorem),
            Paragraph(Text("These results supply genuine finite support and both exact below-start vanishings for the original all-order charged iterate. They do not identify either chart with Ytw of ordinary Y source modes or establish the scalar Gaussian and retained labelled normal-jet recurrences. Those mathematical obligations, the full twisted Jacobi/module law, the full moonshine/string construction and AdS/CFT remain open. Local compilation and emission are not remote required-check, merge or delivery evidence.")))));
}

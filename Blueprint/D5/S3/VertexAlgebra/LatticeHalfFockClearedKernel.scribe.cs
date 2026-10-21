using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockClearedKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Doubled coefficient differences turn the supported native expansion into a finite exchange kernel.",
        H("Finite Cleared Half-Fock Kernels"),
        Blocks(
            Paragraph(Text("For a fixed oscillator polynomial p, coefficientExpansion sums "
                + "series.coeff(d) smul commonKernel(left,right,first+d,second-d,p) over natural d. "
                + "The ordered-diagonal support theorem makes this sum finite even for an arbitrary "
                + "power series. physicalDifference sends a distribution F to "
                + "F(first-2,second)-F(first,second-2). All integer coefficient indices are retained.")),
            Describe.Lean(
                DescribeId.Create("half-fock-physical-difference-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_expansion"),
                H("One physical difference multiplies the series by one minus the square"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying physicalDifference to coefficientExpansion(series,p) "
                    + "gives coefficientExpansion((1-t^2)*series,p) at first-2,second. The proof "
                    + "splits off degrees zero and one and reindexes the remaining finite tail by two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-physical-difference-iterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_iterate"),
                H("Iteration gives the exact doubled first-index shift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural order, the order-th power of physicalDifference "
                    + "gives coefficientExpansion((1-t^2)^order*series,p) at first-2*order,second. "
                    + "Induction preserves the signed integer shifts and the zero-order case."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-cleared-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_expansion"),
                H("The native contraction clears at the absolute Gram order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With N=natAbs(bilinear D left right), iteration applied to "
                    + "halfContraction gives the expansion of clearedPolynomial.toPowerSeries "
                    + "at first-2*N,second. This is a consumed composition of iteration and branch clearing."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-cleared-finite-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.cleared_polynomial_expansion"),
                H("The cleared expansion has a finite polynomial coefficient range"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer gram, the expansion equals the sum over "
                    + "Finset.range(2*gram.natAbs+1), with coefficient clearedPolynomial(gram).coeff(d) "
                    + "and kernel indices first+d,second-d. Coefficients above the degree bound vanish."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-cleared-exchange"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_exchange"),
                H("The cleared native expansions exchange their branches"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The N-fold physical difference of the left/right expansion at "
                    + "first,second equals that of the right/left expansion at second,first, for every "
                    + "oscillator polynomial. Finite range reflection, complementary coefficient "
                    + "reciprocity, common-kernel exchange and symmetry of the integral pairing prove it."))), DescribeRole.Theorem),
            Paragraph(Text("The result is repository-derived from the supported ProductKernel, "
                + "BranchClearing and finite-sum interfaces. It is an oscillator coefficient identity; "
                + "the actual tensor ground factors and their cocycle signs are supplied separately in "
                + "PhysicalLocality. The finite cleared range does not assert finite support of the "
                + "uncleared bivariate kernel or uniformly finite endomorphism-valued support.")))));
}

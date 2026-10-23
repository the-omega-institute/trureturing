using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class BinaryLaurentEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete binary Laurent evaluation and its actual nested-Q application.",
        H("BinaryLaurentEvaluation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-laurent-jump"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation.binary_laurent_jump"),
                H("The complete signed binary Laurent jump"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("The finite Laurent numerator Q has the two original remaining labels y=J and z=B, with arbitrary integer exponents. Multiplication by (y-z)^p is expanded in both genuine Hahn orders. The coefficient difference at the residue indices is a finite sum over exactly those numerator monomials with e(y)+e(z)=-p-n-2. For p<0 each summand is Q(e) choose(e(y),(-p-1).toNat); for p>=0 the complete difference is zero.")),
                    Paragraph(Text("The negative-power computation applies signed_kernel_choose, including negative e(y). At nonnegative diagonal powers, binomial symmetry cancels the two complete coefficients; terms outside the homogeneous fiber vanish in each order. Linearity then evaluates the entire finite numerator. No locality is asserted for a monomial or an ordered half.")),
                    Paragraph(Text("The Reg mirror reconstructs the complete source telescope. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-complete-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation.binary_complete_residue"),
                H("Evaluation of every complete ordinary binary residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For F=Q(y,z)(y-z)^p, contextual_kernel_extraction identifies the complete ordinary outer residue at ell with the two-order Laurent jump at diagonal exponent p+r+ell and remaining mode n-ell. The homogeneous filter e(y)+e(z)=-p-r-n-2 is independent of ell. If p+r+ell<0 the binomial order is (-p-r-ell-1).toNat; otherwise the complete residue vanishes.")),
                    Paragraph(Text("The supported convolution fibers are finite in their actual Hahn carriers. Both ordered terms are combined before the zero tail is asserted. Signed original Laurent powers, empty Q and negative degree fibers are included.")),
                    Paragraph(Text("The Reg mirror reconstructs the complete source telescope. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-fractional-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation.binary_fractional_taylor"),
                H("Contraction of the complete fractional binary residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For F=Q(y,z)/(y-z)^B and any finite fractional cutoff T>=B, supportedQReadout(s,r,T,n) equals binaryTaylor(Q,B,s,r,n). It is zero when r>=B. Otherwise it is the finite sum of Q(e) choose(e(y)-s/2,(B-r-1).toNat) on the exact fiber e(y)+e(z)=B-r-n-2.")),
                    Paragraph(Text("The complete ordinary residues vanish for ell>=B-r. The finite remaining convolution of choose(-s/2,ell) with choose(e(y),B-r-ell-1) contracts by Vandermonde. This is evaluation of a rational binary field and does not identify actual fields with different cutoffs.")),
                    Paragraph(Text("The Reg mirror reconstructs the complete source telescope. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted."))),
                DescribeRole.Theorem))));
}

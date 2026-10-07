using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualProductKernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial convolutions give finite intermediate-vector bounds for the actual common kernel.",
        H("Actual Common Kernel and Intermediate Supports"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("A one-variable polynomial convolution pairs a translated coefficient with "
                + "creationCoeff(alpha,s+d). A two-variable convolution pairs each actual translated "
                + "polynomial monomial with creationCoeff(alpha,u+e_0) creationCoeff(beta,v+e_1). Actual "
                + "rawCoeff and commonKernel on single(delta,p) agree with these convolutions and their "
                + "actual cocycle scalars.")),
            Describe.Lean(
                DescribeId.Create("latticeactualgeneratorlocality-epsilon-skew"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualProductKernel.epsilon_skew"),
                H("The actual cocycle skew law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all charges alpha,beta, epsilon(alpha,beta)=paritySign(B(alpha,beta)) "
                        + "epsilon(beta,alpha), including coincident charges. The released integral cocycle symmetrization "
                        + "proves the sign; it is not a field-locality assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualgeneratorlocality-actual-contraction-binomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualProductKernel.actual_contraction_binomial"),
                H("Actual coefficient contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every integer t and natural j, coefficient j of translatedPolynomial(alpha, "
                        + "creationCoeff(beta,t)) is (-1)^j choose(B(alpha,beta),j) creationCoeff(beta,t-j). The "
                        + "choose function is the integer generalized binomial cast to C."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualproductkernel-kernel-creator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_creator"),
                H("Both independent oscillator shifts of the kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Multiplication of p by X(i,n) gives its actual creator action on the common kernel, "
                        + "minus the alpha pairing times the shift u+n+1, minus the beta pairing times the shift "
                        + "v+n+1. Both translated variables are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualproductkernel-kernel-lower-bounds"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_lower_bounds"),
                H("Separate lower bounds on the actual kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every alpha,beta,delta and polynomial p there exist integers a,b such that "
                        + "commonKernel(alpha,beta,u,v)(single(delta,p))=0 if u<a or v<b. The bounds come from the "
                        + "two coordinate maxima of the finite translatedPairPolynomial support and the actual "
                        + "charge pairings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualproductkernel-ordered-kernel-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualProductKernel.ordered_kernel_finite"),
                H("Both ordered kernels have finite support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all raw indices k,l the sequences K(k-B(alpha,beta)+j,l-j) and "
                        + "K(k-j,l-B(alpha,beta)+j), evaluated on the actual input, have finite support. The "
                        + "independent lower bounds control the decreasing coordinate in each branch."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI "
                + "10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and "
                + "conformal construction. Equation numbers refer to arXiv v1.")),
            Paragraph(Text("The carrier and formal-series interfaces use pinned Mathlib revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.")),
            Paragraph(Text("This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, "
                + "PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, "
                + "string theory, AdS/CFT and physical completion are not proved here.")))));
}

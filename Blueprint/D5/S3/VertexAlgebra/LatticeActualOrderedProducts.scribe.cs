using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualOrderedProductsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual charged ordered products expand in the bounded common kernel.",
        H("Both Actual Charged Ordered Products"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Actual coefficient contraction, finite support on each intermediate vector, and "
                + "induction on oscillator multiplication prove both operator orders. The common kernel has "
                + "the actual output charge alpha+beta+delta. The reverse order is identified through "
                + "kernel swap and the computed cocycle.")),
            Describe.Lean(
                DescribeId.Create("latticeactualorderedproducts-actual-ordered-product"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_ordered_product"),
                H("First actual order in the common kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("rawCoeff(alpha,k) rawCoeff(beta,l) single(delta,p) equals epsilon(alpha,beta) times the "
                        + "finite sum of (-1)^j choose(B(alpha,beta),j) K(k-B(alpha,beta)+j,l-j) on that input. "
                        + "Both intermediate-field truncation and kernel bounds are proved from the actual "
                        + "polynomials."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualorderedproducts-actual-reverse-ordered-product"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_reverse_ordered_product"),
                H("Reverse actual order in the same kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("rawCoeff(beta,l) rawCoeff(alpha,k) single(delta,p) equals epsilon(beta,alpha) times the "
                        + "finite sum with kernel indices (k-j,l-B(alpha,beta)+j). No desired expansion is a "
                        + "premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualorderedproducts-actual-field-ordered-product"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_ordered_product"),
                H("Normalized modes preserve the raw product convention"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every integer m,n substitute k=-m-1 and l=-n-1 in the actual first ordered product. "
                        + "The operator order and both kernel index shifts are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualorderedproducts-actual-field-reverse-ordered-product"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_reverse_ordered_product"),
                H("Normalized reverse product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The same substitution in the proved reverse coefficient product gives F_beta[n] "
                        + "F_alpha[m] on every actual single(delta,p). These are normalized mode identities from the "
                        + "whole ordered-product proof."))),
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

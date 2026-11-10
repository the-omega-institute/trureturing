using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PartitionCollisionExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.";

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary-order quadratic moment expansion by equality partitions.",
        H("Partition collision expansion"),
        Blocks(
            Paragraph(Text(
                "Let the index type be finite, let A be a commutative real algebra, and let ell be any real linear functional on A. "
                + "Suppose Y(d)^2=a*Y(d)+b*1 for every index d. No normalization of ell, centering, independence, or positivity is required. "
                + "All orders, including zero, and empty index types are allowed. "
                + "A partition is represented by a Mathlib Setoid on the positions Fin k; its blocks are its quotient classes. "
                + "Grouping tuples by their equality relation is the classical decomposition of a finite sum into fibers, "
                + "also underlying the set-partition expansion of power sums; see Stanley, Enumerative Combinatorics, volume 1, second edition, "
                + "section 3.1, for the partition lattice. The quadratic moment reduction is the algebraic consequence described below.")),
            Entry("quadratic-power-coeffs", "quadraticPowerCoeffs", "Quadratic remainder coefficients",
                "For real a and b define (u(0),v(0))=(0,1), and (u(m+1),v(m+1))=(a*u(m)+v(m),b*u(m)). "
                + "These are the coefficients of the remainder of X^m modulo X^2-a*X-b.", DescribeRole.Definition),
            Entry("quadratic-power-coeffs-pow", "quadraticPowerCoeffs_pow", "Reduction at every exponent",
                "For every real a,b, every y in A satisfying y^2=a*y+b*1, and every natural m, "
                + "y^m=u(m)*y+v(m)*1. Induction multiplies the preceding expression by y and uses the quadratic relation.", DescribeRole.Theorem),
            Entry("tuple-kernel-patterns", "tupleKernelPatterns", "Realized equality patterns",
                "For a natural order k and finite index type, tupleKernelPatterns is the image of all maps d from Fin k to the index type "
                + "under d mapped to Setoid.ker d. Partitions with more blocks than available indices are absent, since their contribution would be zero.", DescribeRole.Definition),
            Entry("sum-eq-tuple-kernel-sums", "sum_eq_tupleKernel_sums", "Decomposition by equality pattern",
                "For every k, finite index type, additive commutative monoid M and function F from position tuples to M, "
                + "the sum of F over all tuples equals the sum over realized kernel setoids sigma of the sum of F over tuples with kernel exactly sigma. "
                + "This is Mathlib's finite fiber-sum theorem applied to Setoid.ker.", DescribeRole.Theorem),
            Entry("kernel-block-size", "kernelBlockSize", "Block multiplicity",
                "For every k, setoid sigma on Fin k, and quotient class B, kernelBlockSize is the cardinality of the positions whose quotient class is B. "
                + "Every quotient class has a representative, so each such block has positive size.", DescribeRole.Definition),
            Entry("kernel-distinct-moment", "kernelDistinctMoment", "Residual distinct-block moment",
                "For ell, Y, coefficient functions f indexed by Fin k, a setoid sigma and a finite set S of its quotient blocks, "
                + "kernelDistinctMoment sums, over tuples d with kernel exactly sigma, the product over positions i of f(i,d(i)) "
                + "times ell of the product over B in S of Y(d(B.out)). "
                + "The exact-kernel condition says that the tuple is constant on each block and that different blocks receive different indices. "
                + "Thus the positional coefficient product is also the product of the block-aggregated coefficients. "
                + "Every block-injective assignment corresponds to exactly one such tuple; representative choices do not change its values.", DescribeRole.Definition),
            Entry("quadratic-moment-eq-partition-expansion", "quadratic_moment_eq_partition_expansion", "The general collision expansion",
                "For every k, ell, Y, a, b satisfying the quadratic relation and coefficient family f, quadraticFamilyMoment equals "
                + "the sum over sigma in tupleKernelPatterns(k) and all finite subsets S of its quotient blocks of "
                + "the product of u(size(B)) over B in S, times the product of v(size(B)) over B in the complement of S, "
                + "times kernelDistinctMoment(ell,Y,f,sigma,S). The complement is within the finite quotient type. "
                + "Group the positions by their kernel blocks, reduce each block power using the coefficient recurrence, "
                + "expand the product of the resulting two-term sums, and apply linearity. "
                + "The residual moment retains only distinct block values. This gives the quadratic collision reduction at every order.", DescribeRole.Theorem))));
}

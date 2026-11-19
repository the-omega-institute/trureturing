using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class AllPartitionExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.";

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An index-independent enumeration of arbitrary-order collision partitions.",
        H("All partition expansion"),
        Blocks(
            Entry("tuple-kernel-patterns-fin-universal", "tupleKernelPatterns_fin_universal", "Every partition has a finite-label tuple",
                "For every natural k and every setoid sigma on Fin k, sigma belongs to tupleKernelPatterns(k,Fin k). "
                + "The quotient of sigma has at most k elements. Composing its injection into Fin k with the quotient map gives a tuple whose kernel is exactly sigma. "
                + "This includes k=0."),
            Entry("sum-pairing-partition-configurations", "sum_pairing_partition_configurations", "Summing the zero-degree configurations",
                "For any natural k and real-valued function G on partial pairings of Fin k, sum G over all partitions sigma and retained subsets S "
                + "whose retained blocks have size one and whose unretained blocks have size two, evaluating G at their unretained two-element blocks. "
                + "This sum equals the sum of G over all partial pairings, with each counted exactly once. "
                + "The bijection between these configurations and partial pairings introduces no ordering or factorial factor."),
            Entry("quadratic-moment-eq-all-partition-expansion", "quadratic_moment_eq_all_partition_expansion", "The same partition set for every index type",
                "Let the index type be finite, A a commutative real algebra, ell:A->R real linear, and Y(d)^2=a*Y(d)+b*1 for all d. "
                + "For any coefficient family f indexed by Fin k, quadraticFamilyMoment equals the sum over sigma in tupleKernelPatterns(k,Fin k) and all retained block sets S "
                + "of product_(B in S) u(size(B)), times product_(B outside S) v(size(B)), times kernelDistinctMoment(ell,Y,f,sigma,S). "
                + "Here u and v are quadraticPowerCoeffs and size(B)=mult(Quotient.mk sigma,B). "
                + "Every partition absent from the index-type tuple kernels has an empty exact-kernel sum and contributes zero. "
                + "No centering, normalization, positivity or independence is needed."),
            Entry("pairing-partition-coefficient", "pairingPartition_coefficient", "The coefficient of a partial pairing",
                "For any PairingPartitionData D and real a,b, the product of u(size(B)) over its retained blocks "
                + "times the product of v(size(B)) over its unretained blocks equals b^(card(pairingPartitionPairs(D))). "
                + "Every retained size is one, giving u(1)=1; every unretained size is two, giving v(2)=b. "
                + "The bijection with partial pairings preserves the number of unretained blocks."),
            Entry("all-partition-configuration-bound", "all_partition_configuration_bound", "A uniform configuration count",
                "For every natural k, the sum over sigma in tupleKernelPatterns(k,Fin k) of the number of finite subsets of Quotient sigma "
                + "is at most k^k*2^k. The partition set is an image of the k^k functions from Fin k to itself, "
                + "and each quotient has at most k elements, giving at most 2^k retained subsets. "
                + "At k=0 both factors and the configuration count equal one."))));
}

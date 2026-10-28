using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedSignedGyrationEvaluatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CountedSignedGyrationEvaluator",
        H("The same ranked-edge weight in natural coordinates"),
        Blocks(


            Describe.Lean(
                DescribeId.Create("countedsignedgyrationevaluator-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedSignedGyrationEvaluator.wordWeight_keys"),
                H("Transport the existing product-edge order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An edge of R*S is represented by the five natural coordinates source, target, middle vertex, R-half-edge rank and S-half-edge rank. edgeKey obtains the last three from CountedMatrixOverlap.fiberEquiv. The existing fiber_number_lt_iff from CountedOrderTypeGyration identifies their lexicographic order with the existing canonical product-edge number; endpoint order remains source then target. Injectivity and this comparison equivalence transport WordLT, then StrictLeast, then wordWeight. No second product-edge numbering or realization is defined.")),
                    Paragraph(Text("KeyWordLT compares at the first unequal time; KeyLeast compares a word with every nonzero cyclic rotation. keyWeight retains the original complete sum over rotation indices k, including k=0 with its zero contribution, and the signed weight minus k. There is no uniqueness shortcut or test on unlabelled vertex primitivity. This order-transport helper is used in rankedTerm_eq_vectorTerm; it supplies no independent product-ranking theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedsignedgyrationevaluator-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedSignedGyrationEvaluator.rankedTerm_eq_vectorTerm"),
                H("Substitute the recovered ranks into both words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any l in rankVectors S w, reconstruct exactly typeOfRanks S w l. The source key at time t is (a t,a(t+1),b t,0,l t); the target key is (b t,b(t+1),a(t+1),l t,0). The two displayed tuples come from the existing sourceEdge and targetEdge join formulas. The R ranks are zero by construction, and the S ranks are the original l. Applying wordWeight_keys proves equality of the original rankedTerm with vectorTerm, with the same product of minus-one width factors. No support, positivity or square-dimension premise is added to this membership-conditional identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedsignedgyrationevaluator-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedSignedGyrationEvaluator.vectorTerm_zero_of_nonminimal"),
                H("A safe first-triple pruning criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If a source key word is strictly least under rotations, no time slot has a smaller outside-source, outside-target, middle-vertex triple than its time-zero triple. To see this, a smaller triple would give a reverse comparison at coordinate zero against that rotation. A lexicographic comparison in the forward direction either compares at zero, contradicting asymmetry, or has an equal prefix containing zero, contradicting irreflexivity. Therefore a nonminimal first triple forces keyWeight, and hence vectorTerm, to vanish.")),
                    Paragraph(Text("SkeletonMinimal tests only each triple against the first triple. It never orders whole unlabelled skeleton rotations: an earlier rank-label comparison can decide such a comparison before a later vertex difference. Repeated cycles and every allowed rank vector remain. supportedEvaluator_eq_pruned uses this vanishing result to discard exactly the rejected middle words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedsignedgyrationevaluator-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedSignedGyrationEvaluator.signedGyrationLift_eq_supportedEvaluator"),
                H("Exact evaluation of the original polynomial lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every nonzero period d and compatible rectangular pair R:n by m, S:m by n, with R entries zero or one and S entries minus one, zero or one, supportedEvaluator equals signedGyrationLift at Sum.elim of those same matrix entries. It sums outside words a, supported middle words b and dense S rank vectors l using vectorTerm. The support module supplies the dependent-sum reindexing and rankedTerm_eq_vectorTerm supplies equality of each remaining summand. The existing integerGyrationValue definition is this signed lift, so the same equality holds directly for integerGyrationValue.")),
                    Paragraph(Text("The existing rationalGyrationPolynomial_eval_signed already identifies the rational polynomial evaluation with the integer signed lift after casting to the rationals. Combining that result with this equality explains the polynomial-evaluation scope without adding another named theorem. Arbitrary signed integer inputs remain valid for the original polynomial theorem; the sparse evaluator equality here has the stated binary/ternary restrictions. Dimensions may be zero, zeros may occur and matrices may be singular. No invertibility, three-divisibility of d, fixed dimension, residue table or numerical value is assumed."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(
                H("Partition by the first outside vertex"),
                Blocks(
                    Paragraph(Text("For d=k+1, the existing Fin.consEquiv partitions each outside word into its head i and tail of length k. Reindexing its finite sum gives prunedEvaluator(k+1,R,S) as the sum over i of prunedShard(k,R,S,i). The partition permits separate reductions at each first outside vertex. Together with supportedEvaluator_eq_pruned and the equality of integerGyrationValue with its signed lift, it expresses the time and I+T gyration calculations at periods three and six as finite sums of shards. This identity supplies no value for those sums.")),
                    Paragraph(Text("The relation between cyclic rotation, least representatives and signed integer weights is preserved throughout the coordinate change. The derivations use existing finite sums and ordered fibres. They do not establish the original-h theorem, literal Fix(T^6), minimum-six objective, full mod-six law or rho-image exhaustion.")))))));
}

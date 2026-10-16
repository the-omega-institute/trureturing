using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedOrderTypeGyrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite order types of counted cyclic words",
        H("Finite order types of counted cyclic words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countedordertypegyration-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOrderTypeGyration.numbered_word_sum_eq_order_types"),
                H("Order-type decomposition of the integer word sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix arbitrary finite vertex counts n and m, including zero, and a nonzero cycle length d. A numbered product edge is split by the existing CountedMatrixOverlap lexicographic rank: intermediate vertex, first number, second number. Increasing relabelings preserve this exact edge order, the induced word order, primitivity and the forward weight; parallel-edge numbers remain part of every comparison.")),
                    Paragraph(Text("For each pair of vertex words, partition the d first-half slots and d second-half slots by their matrix entry. At each entry the image of the labels, in increasing order, and the surjection onto its ranks recover the labels bijectively. This is the classical ordered-partition decomposition; the number of increasing realizations of width k in a set of size z is the binomial coefficient choose(z,k), using the existing finite-subset enumeration.")),
                    Paragraph(Text("The integer word weight is zero except at a strictly least source word. For that word it sums the negatives of the indices whose target rotations are strictly least. Thus it preserves the forward convention: if rotation k selects the target representative, the forward offset is minus k. Relabeling invariance lets the finite sum over labels be replaced by a sum over rank patterns weighted by a product of binomial coefficients. Unavailable widths contribute zero; empty occurrence sets have width zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedordertypegyration-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOrderTypeGyration.elementary_source_cyclicPath"),
                H("The actual positive recoding at every integer time"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Periodic extension uses Euclidean block addresses at all signed integer times. Legal finite numbered words extend to actual two-sided paths, and finite primitivity is equivalent to minimal shift period d. The elementary homeomorphism sends the original pair (r_t,s_t) to (s_t,r_(t+1)); the extension equality proves that this is the actual positive recoding, with its original direction.")),
                    Paragraph(Text("These are finite combinatorial and dynamical constructions, using classical least representatives and ordered fibers. They do not assert an effective algorithm, a bound for an unbounded family of periods, SGCC, or a novelty claim."))),
                DescribeRole.Theorem))));
}

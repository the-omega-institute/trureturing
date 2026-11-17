using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts;

internal sealed class BinaryCodePerfectRestrictedBasisDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Correctable binary error supports are unique bounded subset sums in a quotient group.",
        H("Binary codes and perfect restricted bases"),
        Blocks(
            Paragraph(Text("Let F2 be ZMod 2. A binary word is a function from Fin n to F2. "
                + "A submodule C identifies words whose difference is a codeword. The coordinate "
                + "vectors therefore define elements of the additive quotient group.")),
            Entry("binary-code-field", "F2", "The binary coefficient field", DescribeRole.Definition,
                "F2 is ZMod 2, the field of two elements."),
            Entry("binary-code-weight", "weight", "The Hamming weight", DescribeRole.Definition,
                "For every natural n and v : Fin n -> F2, weight v is the cardinality of the "
                + "finset of coordinates i for which v i is nonzero."),
            Entry("binary-code-support-word", "word", "The indicator word of a subset", DescribeRole.Definition,
                "For every natural n and S : Finset (Fin n), word S : Fin n -> F2 has value "
                + "one on S and zero outside S."),
            Entry("binary-code-bounded-subsets", "subsets", "All bounded error supports", DescribeRole.Definition,
                "For naturals n and s, subsets n s is the full powerset of Fin n filtered by "
                + "the condition that the subset cardinality is at most s. It includes the empty subset."),
            Entry("binary-code-subset-count", "card_subsets", "Counting all bounded supports", DescribeRole.Theorem,
                "For all naturals n and s, the cardinality of subsets n s equals the sum of "
                + "Nat.choose n k over k in Finset.range (s + 1), namely k = 0 through s. "
                + "The subsets are partitioned by cardinality, and each layer has the corresponding binomial count."),
            Entry("binary-code-perfect-basis", "basis_of_minimum_weight", "Minimum distance and sphere equality", DescribeRole.Theorem,
                "For naturals n and s and C : Submodule F2 (Fin n -> F2), assume 1 <= s, "
                + "every nonzero v in C satisfies 2*s < weight v, and Nat.card ((Fin n -> F2) / C) "
                + "equals the cardinality of subsets n s. Then there exists a finset A of that "
                + "quotient with A.card = n and IsPerfectRestrictedBasis s A. The predicate is "
                + "the original one: every quotient element has exactly one representing subset T "
                + "of A with T.card <= s and sum T equal to that element, including the empty sum. "
                + "A difference between two admissible indicator words has support inside the union "
                + "of the two subsets, of size at most 2*s. The minimum-weight hypothesis forces "
                + "equal quotient sums to have equal supports. Singleton supports show that the "
                + "coordinate classes are distinct. Equality of the finite cardinalities gives "
                + "surjectivity; pulling every subset of A back to its full coordinate preimage "
                + "transfers both existence and uniqueness."))));

    private static DocumentBlock.Describe Entry(string id, string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

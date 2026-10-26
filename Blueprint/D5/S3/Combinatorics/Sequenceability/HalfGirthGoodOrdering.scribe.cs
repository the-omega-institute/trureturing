using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class HalfGirthGoodOrderingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-label Good orders above half girth",
        H("Original-label Good orders above half girth"),
        Blocks(
            Describe.Lean(DescribeId.Create("half-girth-order"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/HalfGirthGoodOrdering.exists_good_order"),
                H("Original-label Good orders above half girth"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "X is finite, m is its cardinality, G is any additive commutative group, and a maps "
                    + "the original indices injectively to nonzero labels. The integer k satisfies "
                    + "2 ≤ k ≤ m and m < 2k. Every nonempty proper original-index subset with sum zero "
                    + "has cardinality at least k. The resulting list is a permutation of all original "
                    + "indices. Good has its existing meaning: every nonempty proper consecutive "
                    + "subword of the mapped list has nonzero original-group sum."))), DescribeRole.Theorem),
            Paragraph(Text(
                "If the complete proper-zero family is empty, any enumeration works. Otherwise choose "
                + "a minimum member S of cardinality K, and fix any order C of its complement, of length "
                + "l < K. For nonempty proper A ⊂ S and B ⊆ C with equal sums, the original-index set "
                + "(S \\ A) ∪ B is a nonempty proper zero subset. Minimality gives |A| ≤ |B|. This rank "
                + "constraint is derived from the complete zero family.")),
            Paragraph(Text(
                "Build a list r of S greedily. After d chosen entries, a suffix of C can forbid the "
                + "next entry only if its length is at least d+1, by the replacement rank constraint. "
                + "Each such suffix sum excludes at most one remaining label, by injectivity. The "
                + "remaining set has K-d entries and at most max(l-d,0) forbidden values, so an entry "
                + "exists. The final entry needs no avoidance condition. Thus every nonempty proper "
                + "prefix of r has sum distinct from every nonempty suffix of C.")),
            Paragraph(Text(
                "In C followed by reverse(r), intervals internal to either block are shorter than K, "
                + "except the whole zero block S. For a crossing interval, its S prefix has sum equal "
                + "to the negative of the complementary r prefix. Greedy avoidance excludes zero; "
                + "when the whole S block is used, the nonempty C suffix has length below K. Hence S "
                + "is the sole proper zero interval. Equivalently the only collision between distinct "
                + "prefix sums is at the start and end of S. The proof uses the existing prefix-sum "
                + "criterion in SeparatedPrefixReflection.good_iff.")),
            Paragraph(Text(
                "Swap the last complement index c with the first reversed-S index s. Only the prefix "
                + "value at this boundary changes. On its left, every resulting interval has length "
                + "at most l < K. On its right, an interval starting at c has length at most K. A zero "
                + "one must use all of S except s and therefore has sum a(c)-a(s), which is nonzero. "
                + "This excludes all collisions and proves Good for the literal swapped enumeration. "
                + "No auxiliary labels, zero-total premise, torsion restriction, or fixed bound on m "
                + "is used. The empty-family branch includes k=m.")),
            Paragraph(Text(
                "For the integral application, let H cover every permutation by a nonempty proper "
                + "interval, and let M be the exact integer span of its Boolean rows in the free "
                + "integer module on X. The quotient labels are e_i+M. Submodule.Quotient.mk_eq_zero "
                + "and Submodule.ker_mkQ identify their zero sums with literal membership in M. "
                + "Absence of original units and differences makes these labels nonzero and injective. "
                + "If M contained no nonempty Boolean row of size at most floor(m/2), the complete "
                + "quotient zero family would satisfy the theorem with k=floor(m/2)+1. Its Good "
                + "enumeration contradicts coverage by H. Thus an actual short Boolean row lies in M, "
                + "with integer coefficients on the original H rows, as expressed by Submodule.mem_span_image_iff_exists_fun. This is an application of exact "
                + "quotient suppliers, with no rational saturation. The short row need not be a row "
                + "of H or a unit or difference. The unrestricted Good and primitive-blocker problems "
                + "remain open when the complete zero family has minimum size at most m/2. "
                + "No claim of novelty, consensus, or resolution of those unrestricted problems is made.")))));

    private static Formula Statement() => Disp(A("X", C("FiniteType"), A("G", C("AddCommGroup"),
        A("a", C("Map", FormulaDsl.Id("X"), FormulaDsl.Id("G")), A("k", C("Nat"),
            Imp(Hypotheses(),
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("w"), C("List", FormulaDsl.Id("X")),
                    AndR(C("Perm", FormulaDsl.Id("w"), C("univToList", FormulaDsl.Id("X"))),
                        C("Good", C("map", FormulaDsl.Id("a"), FormulaDsl.Id("w")))))))))));

    private static Formula Hypotheses() => AndR(C("Injective", FormulaDsl.Id("a")),
        AndR(A("x", FormulaDsl.Id("X"), new Formula.Not(E(C("a", FormulaDsl.Id("x")), D(0)))),
            AndR(C("Le", D(2), FormulaDsl.Id("k")),
                AndR(C("Le", FormulaDsl.Id("k"), C("card", FormulaDsl.Id("X"))),
                    AndR(C("Lt", C("card", FormulaDsl.Id("X")), C("mul", D(2), FormulaDsl.Id("k"))),
                        A("T", C("Finset", FormulaDsl.Id("X")),
                            Imp(AndR(C("Nonempty", FormulaDsl.Id("T")),
                                    AndR(new Formula.Not(E(FormulaDsl.Id("T"), C("univ"))),
                                        E(C("sum", FormulaDsl.Id("T"), FormulaDsl.Id("a")), D(0)))),
                                C("Le", FormulaDsl.Id("k"), C("card", FormulaDsl.Id("T"))))))))));

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula AndR(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula E(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}

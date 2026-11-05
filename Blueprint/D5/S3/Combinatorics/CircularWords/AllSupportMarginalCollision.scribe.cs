using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class AllSupportMarginalCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/AllSupportMarginalCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On every finite labeled support of size at least four, distinct rational probability laws on oriented cycles have all one-label deletion marginals equal.",
        H("All-Support Circular Marginal Collisions"),
        Blocks(
            Paragraph(Text("Let alpha be any type with decidable equality and A any finite set of labels with at least four elements. "
                + "Cycle(alpha) is Mathlib's quotient of lists by rotation: orientation is retained, and reversal is not identified. "
                + "A rational finitely supported law is a Finsupp from these actual cycles to the rationals. "
                + "Deleting label i filters that label from a cycle; pushforward is the actual Finsupp.mapDomain(delete(i)). "
                + "Mass is the value at unit of the pushforward along the constant map to unit.")),
            Describe.Lean(DescribeId.Create("all-support-marginal-collision"),
                DeclarationHandle.Create(Prefix + "all_support_marginal_collision"),
                H("Disjoint Laws with Every Individual Deletion Marginal Equal"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There exist laws mu and nu on Cycle(alpha). Every cycle in the union of their Finsupp supports "
                        + "has no repeated label and has toFinset exactly A. For every cycle C, both mu(C) and nu(C) are nonnegative. "
                        + "Each law has mass one, and their actual cycle supports are disjoint. For every i in A, "
                        + "the two entire deletion pushforward laws are equal. Thus every label's marginal distribution agrees; "
                        + "no paired or other joint observations from a common sample are supplied by the theorem.")),
                    Paragraph(Text("The construction first builds a private Trade(B,m,n) on linear words for every finite B with at least two labels. "
                        + "Its invariants are exact support B without repetition, nonnegative coefficients, mass one on each side, "
                        + "disjoint word supports, equality after erasing each label of B, and equality after sending words to Cycle.ofList. "
                        + "For B={a,b} with a distinct from b, the seed puts unit mass on [a,b] and [b,a] respectively.")),
                    Paragraph(Text("For a fresh label x, let P_x prepend x and Q_x append x. The recursive signed interchange sets "
                        + "m' to one half of (push(P_x,m)+push(Q_x,n)) and n' to one half of (push(P_x,n)+push(Q_x,m)). "
                        + "Freshness preserves exact support and no repetition, and averaging preserves nonnegativity and mass one. "
                        + "A word starting with x cannot equal a word ending with x when its remaining nonempty word avoids x. "
                        + "Together with the old disjointness and injectivity at each endpoint, this proves the new word supports disjoint. "
                        + "Erasing x gives the same average of m and n on both sides. Erasing an old label commutes with both endpoint maps, "
                        + "so the previous erasure equality proves the remaining cancellations.")),
                    Paragraph(Text("The additional circular invariant is essential. The words x::L and L++[x] represent the same oriented cycle. "
                        + "After Cycle.ofList pushforward the two recursive averages therefore agree by interchange of their summands. "
                        + "Strong induction on finite supports constructs these word trades for arbitrary size; it is used in the public theorem's proof.")),
                    Paragraph(Text("Choose p in A and put B=A.erase(p). Push the two word laws forward by L mapped to the cycle of p::L. "
                        + "The fresh anchor gives exact cycle support A and preserves nonnegativity and normalization. "
                        + "CyclicInsertionGap.anchored_coe_injective shows that equality of two such cycles forces equality of their words, "
                        + "so disjoint word supports give disjoint actual cycle supports. For i distinct from p, deleting i commutes with anchoring "
                        + "and uses the word-erasure invariant. Deleting p leaves Cycle.ofList(L), so equality in this case follows from the extra circular invariant. "
                        + "This covers every label in A, including the chosen anchor."))), DescribeRole.Theorem),
            Paragraph(Text("This is a repository-derived construction. The stated range is cardinality at least four; "
                + "no three-label strengthening or sharp support-cardinality bound is asserted. "
                + "The result concerns a family of separate marginals, and makes no assertion that those marginals determine a joint observation law.")),
            Paragraph(Text("The literature check distinguishes nearby reconstruction models. The publisher abstract of Permutation Reconstruction "
                + "(DOI 10.37236/1149) deletes entries of a linear permutation and renumbers the remaining labels. "
                + "Permutation Reconstruction from Minors (DOI 10.37236/1092) likewise uses order-preserving renumbering after deletions. "
                + "Reconstructing Permutations from Cycle Minors (DOI 10.37236/108) uses deletion from the disjoint-cycle decomposition "
                + "of a permutation and reduces larger labels by one. These verified abstracts do not directly state the present fixed-label "
                + "probability-law theorem on a single oriented cyclic word. Their full theorems are not attributed as this result. "
                + "No literature novelty claim is made. The specific connection to Diaconis and Sturmfels, Algebraic algorithms for sampling "
                + "from conditional distributions (DOI 10.1214/aos/1030563990), remains a lead: its full text was not obtained in this check.")))));

    private static Formula Statement()
    {
        Formula a = F.Id("alpha"), set = F.Id("A"), m = F.Id("mu"), n = F.Id("nu"), c = F.Id("C"), i = F.Id("i");
        Formula cycle = Call("Cycle", a), law = Call("Finsupp", cycle, Call("Rat"));
        Formula supports = All("C", cycle, Imp(In(c, Call("union", Call("support", m), Call("support", n))),
            And(Call("Nodup", c), Eq(Call("toFinset", c), set))));
        Formula nonnegative = All("C", cycle, And(Le(D(0), Call("mu", c)), Le(D(0), Call("nu", c))));
        Formula massM = Call("value", Call("mapDomain", Call("constantUnit"), m), Call("unit"));
        Formula massN = Call("value", Call("mapDomain", Call("constantUnit"), n), Call("unit"));
        Formula marginals = All("i", a, Imp(In(i, set),
            Eq(Call("mapDomain", Call("delete", i), m), Call("mapDomain", Call("delete", i), n))));
        Formula conclusion = Ex("mu", law, Ex("nu", law,
            And(supports, And(nonnegative, And(Eq(massM, D(1)), And(Eq(massN, D(1)),
                And(Call("Disjoint", Call("support", m), Call("support", n)), marginals)))))));
        return Disp(All("alpha", Call("Type"), Seq(OpenBracket, Call("DecidableEq", a), CloseBracket, Sp,
            All("A", Call("Finset", a), Imp(Le(D(4), Call("card", set)), conclusion)))));
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
}

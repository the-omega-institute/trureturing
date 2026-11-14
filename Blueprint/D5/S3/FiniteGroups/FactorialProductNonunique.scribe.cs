using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FactorialProductNonuniqueDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/FactorialProductNonunique.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/aivazidis2023commontransversal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The products of n!/n^n do not uniquely determine a finite set of distinct integers greater than one.",
        H("Nonuniqueness of factorial-weight products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorial-product-uniqueness-claim"),
                DeclarationHandle.Create(Owner + "claim"), H("The unrestricted set assertion"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Problem 5.6 of Aivazidis, Loukaki and Müller asks whether equal finite "
                    + "products of f(m)=Gamma(m+1)/m^m force the same distinct integer parameters "
                    + "after reordering. For integers m greater than one, f(m)=m!/m^m. "
                    + "The claim quantifies every two finite sets of natural numbers whose "
                    + "members exceed one. It imposes no bound, equal-cardinality hypothesis, "
                    + "prime restriction or group realization. The function orbitWeight is "
                    + "the original rational factorial-weight definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("factorial-product-uniqueness-refuted"),
                DeclarationHandle.Create(Owner + "result"), H("Two disjoint sets with equal products"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Open, ClaimBody(), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take A={10,17,21,23,24,27,38,45,46,48,56,65,68,77,80,84,95,141} "
                        + "and B={11,16,20,22,25,26,39,44,47,49,57,64,69,76,81,85,94,140}. "
                        + "Both sets have eighteen elements, they are disjoint, and every "
                        + "member is greater than one. Their factorial-weight products are "
                        + "equal as exact rational numbers. Since ten belongs to A and not B, "
                        + "the equality cannot arise from reordering the parameters.")),
                    Paragraph(Text(
                        "The equality can also be understood using adjacent pairs: "
                        + "f(n+1)/f(n)=(n/(n+1))^n. The products of these ratios agree for "
                        + "the starting sets {16,20,22,26,44,64,76,94,140} and "
                        + "{10,24,38,46,48,56,68,80,84}. The pairs have distinct even starts "
                        + "and hence no common endpoints. Crossing numerators and denominators "
                        + "gives precisely A and B. The proof checks the displayed factorial "
                        + "products directly in rational arithmetic; no approximation enters.")),
                    Paragraph(Text(
                        "This refutes the full unrestricted uniqueness assertion, including "
                        + "the interpretation requiring all parameters on both sides to be "
                        + "distinct. It does not refute Theorem 4.6, which requires distinct primes on one side and allows arbitrary integer parameters on the other side. "
                        + "No minimality, composite-only strengthening or worldwide priority "
                        + "claim is asserted.")),
                    Paragraph(Text(
                        "The displayed data have a stronger finite certificate. Let U={16,20,22,26,44,64,76,94,140} "
                        + "and V={10,24,38,46,48,56,68,80,84}. These are disjoint sets of nine even starts, "
                        + "and A=V union (U+1), B=U union (V+1). The eighteen adjacent pairs are therefore disjoint, "
                        + "so both A and B have cardinality 18, A and B are disjoint, and each parameter is greater than one. "
                        + "Each side selects nine upper and nine lower endpoints from the same pairs, giving sum 956+9=965. "
                        + "For each of the ten primes 2,3,5,7,11,13,17,19,23,47, the exponent "
                        + "sum n times (v_p(n)-v_p(n+1)) agrees for U and V; no other prime occurs in the displayed adjacent factors. "
                        + "The resulting rational certificate is 2^1150 7^44 divided by "
                        + "3^326 5^42 11^10 13^38 17^16 19^18 23^22 47^46.")),
                    Paragraph(Text(
                        "The same equality extends along every finite common extension. If C is finite and disjoint from A union B, "
                        + "then A union C and B union C remain distinct, have equal actual factorial-weight products, and have equal sums "
                        + "965 plus the sum of the elements of C. Their symmetric difference is still A union B and has cardinality 36. "
                        + "For representations by integers greater than one, require every member of C to exceed one. For example C={142,...,141+(k-18)} is disjoint from A union B and has cardinality k-18, giving every k at least 18, including empty C at k=18. When k is greater than 18 the two extensions share C; "
                        + "the extension is not claimed to be disjoint.")),
                    Paragraph(Text(
                        "For every fixed k at least 19, choose a finite D disjoint from A union B with cardinality k-19 and then choose each integer c "
                        + "above every member of A union B union D. The two k-element sets A union D union {c} and B union D union {c} have equal sums within each pair "
                        + "and common positive rational product F(A)F(D)orbitWeight(c). Choose D={142,...,141+(k-19)}, with D empty at k=19. Its finite product and F(A) are positive. For positive c the adjacent ratio lies strictly between zero and one; multiplication by the fixed positive F(A)F(D) preserves strict decrease. Thus the map from the unbounded integer tail to these product values is injective, and its image is infinite. The adjacent-ratio identity gives positivity and strict decrease "
                        + "on the positive domain, so these values are pairwise different as c varies. The sums may vary with c; no fixed-sum infinitude claim is made.")),
                    Paragraph(Text(
                        "The same identity gives the complete coordinate comparison: for strictly increasing integer lists a and b of equal length, "
                        + "with every entry greater than one and a_i less than or equal to b_i, the product of the weights at a is at least the product at b, "
                        + "with equality exactly when all coordinates agree. The empty-list boundary is the empty product 1 at length zero, where both products are 1 and coordinate equality is vacuous. "
                        + "Strict decrease is asserted only for positive arguments: orbitWeight 0 and orbitWeight 1 are both 1, so a global strictness claim is false.")),
                    Paragraph(Text(
                        "The decreasing-vector witness is incomparable in weak majorisation: its first partial sums are 141 greater than 140, while its ninth partial sums are 714 less than 715. "
                        + "This is a finite qualification of the source comparison, not a generic majorisation theorem or a refutation of Appendix A. "
                        + "The journal Problem 5.6, arXiv v2 Problem 5.6 and arXiv v1 Problem 12.6 are the covered source questions. "
                        + "Problems 5.1-5.5 and 5.7-5.8, group realization, least counterexample cardinality, minimum maximum parameter, and all-composite restrictions remain outside this result."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alm2024-factorial-product-uniqueness"),
                    ResolutionKind.Refuted)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula AboveOne(Formula a) => All("m", Nat(), Imp(
        new Formula.Relation(F.Id("m"), FormulaRelationOperator.MemberOf, a),
        new Formula.Relation(D(1), FormulaRelationOperator.LessThan, F.Id("m"))));
    private static Formula Product(Formula a) => Seq(new Formula.Subscript(Prod,
        new Formula.Relation(F.Id("m"), FormulaRelationOperator.MemberOf, a)),
        Call("orbitWeight", F.Id("m")));
    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        return All("A", Call("Finset", Nat()), All("B", Call("Finset", Nat()),
            Imp(AboveOne(a), Imp(AboveOne(b), Imp(Eq(Product(a), Product(b)), Eq(a, b))))));
    }
}

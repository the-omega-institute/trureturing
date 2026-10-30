using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class LazyTwoCausalJOneFacetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Observer/abbottwechscostabranciard2017gmnc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The lazy two-causal inequality J1 induces a facet for every party count at least two.",
        H("A facet of every lazy two-causal polytope"),
        Blocks(
            Definition("lazy-two-causal-strategy", "A deterministic lazy two-causal strategy",
                "IsLazyTwoCausalStrategy", StrategyFormula(), AssessedProvenance.FromLiterature(Source),
                "Represent a binary input by its support t and a binary output by its support f(t), "
                    + "both finite subsets of Fin n. The first group k must be nonempty and proper. "
                    + "Laziness means f(t) is contained in t. The outputs in k depend only on the inputs "
                    + "in k: equal intersections of t and u with k give equal intersections of f(t) and f(u) with k. "
                    + "The complementary group may depend on the entire input. This is the deterministic "
                    + "specialization of Definition 2, combined with the lazy output convention "
                    + "(genuine_multi_noncausal.tex, lines 146–154 and 213–214)."),
            Definition("two-causal-polytope", "The convex hull of deterministic correlations",
                "twoCausalPolytope", PolytopeFormula(), AssessedProvenance.FromLiterature(Source),
                "A table p(t,a) gives the probability of output support a at input support t. "
                    + "The deterministic table labelKernel f has entry one when f(t) = a and zero otherwise. "
                    + "Taking the real convex hull over every first group k and every strategy f gives "
                    + "the lazy two-causal polytope. Its tables are nonnegative, sum to one for each input, "
                    + "and vanish unless a is contained in t. Definition 2 gives the convex decomposition; "
                    + "the deterministic description is stated in genuine_multi_noncausal.tex, lines 225–227. "
                    + "The definition also applies to n below two, when there is no nonempty proper first group."),
            Definition("j-one", "The first generalized causal functional",
                "jOne", JOneFormula(), AssessedProvenance.FromLiterature(Source),
                "Sum p(k,k) over all nonempty proper input supports k, then subtract the full-input, "
                    + "full-output probability. For a lazy table, at input support k every output outside k "
                    + "is zero. Thus p(k,k) is exactly the marginal probability that every party in k "
                    + "outputs one. This is J₁(n) from inequality (10) "
                    + "(genuine_multi_noncausal.tex, lines 333–337). The functional is defined on every real table."),
            Definition("claim", "Validity and a face of codimension one",
                "claim", Equivalence(Local("claim"), ClaimBody()), AssessedProvenance.FromRepo(Source),
                "For each natural n at least two, J₁ is nonnegative on the entire lazy two-causal polytope, "
                    + "and its zero face has affine dimension one less than the polytope. Here vectorSpan "
                    + "is the linear span of differences of points, so its real finrank is the affine dimension "
                    + "for these nonempty sets. The dimensions and the added one are natural numbers. "
                    + "This expresses the all-party facet question in genuine_multi_noncausal.tex, lines 343–344; "
                    + "it concerns the lazy binary scenario and J₁ alone."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The inequality is facet inducing for every n at least two"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The defining finite sum makes J₁ a real linear functional. For n ≥ 2, a singleton "
                            + "provides a nonempty proper first group. Consider a deterministic strategy f "
                            + "with first group k. If f sends the full input support to the full output support, "
                            + "independence of the first group's outputs from the complementary inputs forces "
                            + "f(k) = k, using laziness to exclude outputs outside k. Consequently its full-input, "
                            + "full-output probability is at most p(k,k). All diagonal probabilities are "
                            + "nonnegative, and the sum defining J₁ includes this term. Thus J₁ ≥ 0 at every "
                            + "deterministic strategy. The nonnegative half-space of a linear functional is "
                            + "convex, so the inequality holds throughout the convex hull.")),
                    Paragraph(Text(
                        "Every table in the polytope vanishes at (t,a) when a is not contained in t, "
                            + "and each row sums to one; both conditions hold for deterministic tables and "
                            + "are preserved by convex combinations. Differences of tables therefore vanish "
                            + "at the same forbidden coordinates and have row sums zero. Restrict such a "
                            + "difference to the coordinates (t,a) with a nonempty and contained in t. "
                            + "This restriction is injective: forbidden coordinates are already zero, "
                            + "and the empty-output coordinate in each row is determined by its zero row sum. "
                            + "If r is the number of these coordinates, the direction space of the polytope "
                            + "has dimension at most r.")),
                    Paragraph(Text(
                        "Let Z be the deterministic correlation whose output support is always empty. "
                            + "It is two-causal for any nonempty proper first group and has J₁(Z) = 0. "
                            + "For nonempty a strictly contained in t, let V indexed by (t,a) output a "
                            + "exactly at input t and the empty set at every other input. Choose the "
                            + "complement of a as its first group; this group is nonempty and proper, "
                            + "and its outputs are always zero. Laziness follows from a being contained "
                            + "in t. Every nonempty diagonal probability vanishes, including the full-input, "
                            + "full-output probability, so V also lies on the zero face.")),
                    Paragraph(Text(
                        "For a nonempty proper group k, define a further strategy B indexed by k. "
                            + "At input t it outputs k if k is contained in t, and otherwise gives no "
                            + "outputs in k; it additionally outputs the complement of k exactly when t "
                            + "is the full support. These outputs are lazy, and those in k depend only "
                            + "on t intersected with k. At full input it outputs the full support. Among "
                            + "nonempty proper diagonal coordinates its only nonzero entry is p(k,k) = 1. "
                            + "The positive sum and the subtracted term are therefore both one, placing B "
                            + "on the zero face.")),
                    Paragraph(Text(
                        "Index face points by all r reduced coordinates except the full-input, "
                            + "full-output pair. Use B indexed by t when a = t, and V indexed by (t,a) "
                            + "when a differs from t. Subtract Z from each point. For an off-diagonal "
                            + "index, its difference has value one at its own reduced coordinate and zero "
                            + "at every other indexed coordinate. At any proper diagonal coordinate (k,k), "
                            + "the difference indexed by (k,k) is one and all other differences are zero. "
                            + "In a linear relation, evaluation first at these diagonal coordinates makes "
                            + "all diagonal coefficients zero. Evaluation at each off-diagonal coordinate "
                            + "then makes the remaining coefficients zero. The differences are linearly "
                            + "independent.")),
                    Paragraph(Text(
                        "For n ≥ 2 the omitted full pair is a reduced coordinate, so the number m "
                            + "of face points satisfies m + 1 = r. Each of the m independent differences "
                            + "belongs to the direction space of the zero face, since both its endpoints "
                            + "lie there. The face dimension is therefore at least m.")),
                    Paragraph(Text(
                        "The identity strategy f(t) = t is two-causal. Its J₁ value is the number "
                            + "of nonempty proper groups minus one. Any such group and its complement "
                            + "are distinct nonempty proper groups, so this value is strictly positive. "
                            + "Differences of points on the zero face lie in the kernel of J₁. The "
                            + "identity correlation minus Z belongs to the polytope's direction space "
                            + "and has positive J₁ value, so it does not belong to the face's direction "
                            + "space. The latter is thus a proper subspace, and its dimension plus one "
                            + "is at most the polytope dimension.")),
                    Paragraph(Text(
                        "Combine the upper bound r for the polytope dimension, the lower bound m "
                            + "for the face dimension, the identity m + 1 = r, and the strict dimension "
                            + "inequality. They force the face dimension plus one to equal the polytope "
                            + "dimension. Together with validity, this proves the stated facet property "
                            + "for every n ≥ 2."))),
                DescribeRole.Theorem))));

    private static Formula StrategyFormula()
    {
        Formula locality = All("t", Support(), All("u", Support(), Arrow(
            Equal(Intersection(X("t"), X("k")), Intersection(X("u"), X("k"))),
            Equal(Intersection(At(X("f"), X("t")), X("k")),
                Intersection(At(X("f"), X("u")), X("k"))))));
        Formula conditions = And(At(Qualified("Finset", "Nonempty"), X("k")),
            And(NotEqual(X("k"), FullSupport()),
                And(All("t", Support(), SubsetOf(At(X("f"), X("t")), X("t"))), locality)));
        return All("n", Naturals(), All("k", Support(), All("f", StrategyType(),
            Equivalence(LocalCall("IsLazyTwoCausalStrategy", X("k"), X("f")), conditions))));
    }

    private static Formula PolytopeFormula()
    {
        Formula vertices = SetOf("p", Table(), Some("k", Support(), Some("f", StrategyType(),
            And(LocalCall("IsLazyTwoCausalStrategy", X("k"), X("f")),
                Equal(X("p"), At(Qualified("D5", "S3", "TotalVariation", "Equality",
                    "FiberwiseEqualDistanceLift", "labelKernel"), X("f")))))));
        return All("n", Naturals(), Equal(Typed(LocalCall("twoCausalPolytope", X("n")),
            At(Qualified("Set"), Table())), At(Qualified("convexHull"), Reals(), vertices)));
    }

    private static Formula JOneFormula()
    {
        Formula groups = At(Qualified("Finset", "filter"), LambdaOf("k", Support(),
            And(At(Qualified("Finset", "Nonempty"), X("k")), NotEqual(X("k"), FullSupport()))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), Support())));
        Formula sum = At(Qualified("Finset", "sum"), groups,
            LambdaOf("k", Support(), At(X("p"), X("k"), X("k"))));
        return All("n", Naturals(), All("p", Table(), Equal(
            Typed(LocalCall("jOne", X("p")), Reals()),
            Subtract(sum, At(X("p"), FullSupport(), FullSupport())))));
    }

    private static Formula ClaimBody()
    {
        Formula polytope = LocalCall("twoCausalPolytope", X("n"));
        Formula face = Intersection(polytope, SetOf("p", Table(),
            Equal(LocalCall("jOne", X("p")), Typed(D(0), Reals()))));
        Formula validity = All("p", Table(), Arrow(Member(X("p"), polytope),
            LE(Typed(D(0), Reals()), LocalCall("jOne", X("p")))));
        return All("n", Naturals(), Arrow(LE(Typed(D(2), Naturals()), X("n")),
            And(validity, Equal(Add(Dimension(face), Typed(D(1), Naturals())), Dimension(polytope)))));
    }

    private static DocumentBlock Definition(string id, string title, string declaration,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Contextuality",
        "LazyTwoCausalJOneFacet", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Support() => At(Qualified("Finset"), At(Qualified("Fin"), X("n")));
    private static Formula StrategyType() => Arrow(Support(), Support());
    private static Formula Table() => Arrow(Support(), Arrow(Support(), Reals()));
    private static Formula FullSupport() => Typed(Qualified("Finset", "univ"), Support());
    private static Formula Dimension(Formula set) => At(Qualified("Module", "finrank"), Reals(),
        At(Qualified("CoeSort", "coe"), At(Qualified("vectorSpan"), Reals(), set)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, Typed(X(name), type), Sp, Mid, Sp, Parenthesized(condition), CloseBrace);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Intersection(Formula left, Formula right) => At(Qualified("Inter", "inter"), left, right);
    private static Formula SubsetOf(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Subseteq, Sp, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class MultivariateOccupancyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.";
    private static readonly LibraryNoteRef Davies = LibraryNoteRef.Create("D5/L/StatisticalMechanics/davies2026multivariateoccupancy");
    private static readonly LibraryNoteRef Lee = LibraryNoteRef.Create("D5/L/StatisticalMechanics/lee2026multivariateindependence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-vertex star with fugacities (15,2,2) has expected independent-set size 9/8, below the proposed degree-sequence lower bound 259/230.",
        H("A counterexample to the multivariate hard-core occupancy bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("multivariate-occupancy-expected-size"),
                DeclarationHandle.Create(Prefix + "expectedSize"), H("Expected independent-set cardinality"),
                StatementSource.FromAuthor(ExpectedSizeFormula()), AssessedProvenance.FromLiterature(Davies),
                Blocks(Paragraph(Text("Davies, Sandhu, Seo and Tan, arXiv:2605.05149v1, page 1, Section 1: \"For a fugacity vector λ ∈ [0, ∞)^V we define for any I ∈ I(G) the measure\" P_{G,λ}(I) = (1/Z_G(λ)) ∏_{v∈I} λ_v, \"where Z_G(λ) = Σ_{J∈I(G)} ∏_{v∈J} λ_v is the normalizing constant known as the partition function that makes this a probability measure.\" Here Fin n labels all vertices; configurations(G,univ(Fin n)) is the existing family of actual independent subsets, partition is its existing product-weight sum, and ofNat embeds cardinality into R. The numerator counts each configuration once per occupied vertex. Division is in R. For positive fugacities the empty configuration gives partition at least one, so this normalized sum is the expectation under the displayed measure."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-occupancy-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The proposed bound on the positive orthant"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Davies),
                Blocks(Paragraph(Text("Davies, Sandhu, Seo and Tan, arXiv:2605.05149v1, page 2, Section 1 after Theorem 1: \"Strengthening the conjecture, we believe that the multivariate version should hold for any λ in the positive orthant.\" \"The bound in Theorem 1 is tight by the example of a disjoint union of complete graphs (such that λ is constant on each component), though we believe that the upper bound on the entries of λ can be removed.\" Lee and Seo, arXiv:2602.02450v2, page 16, Section 5, Occupancy fractions: \"Having seen the Davies–Kang conjecture, it seems plausible to look for a strengthening of Theorem 1.1 in terms of occupancy fractions.\" Their (5.2) reads α_G(t; λ) ≥ (1/|V(G)|) Σ_{v∈V(G)} α_{K_{d_v+1}}(tλ_v), t ∈ R_{≥0}, λ ∈ (R_{≥0})^{V(G)}. At t = 1, multiply by |V(G)| to obtain the displayed claim, with α_{K_{d+1}}(x) = x/(1+(d+1)x) as in (5.1). This encodes the strictly positive orthant proposed by Davies et al., which is a subset of the nonnegative orthant of Lee and Seo. Every n, simple graph and positive fugacity vector is quantified. The anonymous DecidableRel instance supplies adjacency decisions; classical decidability supplies an instance for every graph. The empty graph is also included. The degree is its natural-number degree embedded into R by ofNat; the addition, multiplication and division in the bound are real operations."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-occupancy-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The three-vertex star refutes the bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Davies, Lee),
                Blocks(Paragraph(Text("Take Mathlib's starGraph on Fin 3 centered at 0 and set lam(0) = 15, lam(1) = lam(2) = 2. Its independent subsets are exactly the empty set, {0}, {1}, {2} and {1,2}; their product weights are 1,15,2,2,4. The partition is 24 and the cardinality-weighted sum is 27, giving expectedSize = 27/24 = 9/8. The degrees are 2,1,1, so the proposed lower bound is 15/46 + 2/5 + 2/5 = 259/230. The difference expectedSize minus this bound is -1/920. All fugacities are positive, contradicting the universal claim. The restricted small-fugacity theorem and the univariate Davies–Kang conjecture are separate statements."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("davies-sandhu-seo-tan-2026-multivariate-occupancy-refutation"),
                    ResolutionKind.Refuted))), []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), To, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula OfNat(Formula a) => Call("ofNat", a);
    private static Formula Relation(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, Parenthesized(body));
    private static Formula ProductOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Prod, index), Sp, Parenthesized(body));
    private static Formula Context(Formula body)
    {
        Formula n = F.Id("n"), g = F.Id("G");
        return All("n", Nat(), All("G", Call("SimpleGraph", FinOf(n)),
            Seq(OpenBracket, Call("DecidableRel", Call("Adj", g)), CloseBracket, Comma, Sp,
                All("lam", Arr(FinOf(n), Real()), body))));
    }
    private static Formula ExpectedSizeFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), lam = F.Id("lam"), s = F.Id("S"), v = F.Id("v");
        Formula domain = Call("univ", FinOf(n));
        Formula product = ProductOver(Relation(v, FormulaRelationOperator.MemberOf, s), Apply(lam, v));
        Formula numerator = SumOver(Relation(s, FormulaRelationOperator.MemberOf,
            Call("configurations", g, domain)), Mul(OfNat(Call("card", s)), product));
        return Disp(Context(Relation(Call("expectedSize", g, lam), FormulaRelationOperator.Equal,
            new Formula.Fraction(numerator, Call("partition", g, domain, lam)))));
    }
    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), lam = F.Id("lam"), v = F.Id("v");
        Formula positive = All("v", FinOf(n), Relation(D(0), FormulaRelationOperator.LessThan, Apply(lam, v)));
        Formula denominator = Add(D(1), Mul(Parenthesized(Add(OfNat(Call("degree", g, v)), D(1))), Apply(lam, v)));
        Formula bound = SumOver(Seq(v, Colon, FinOf(n)), new Formula.Fraction(Apply(lam, v), denominator));
        Formula inequality = Relation(bound, FormulaRelationOperator.LessThanOrEqual, Call("expectedSize", g, lam));
        Formula body = new Formula.Logic(Parenthesized(positive), FormulaLogicOperator.Implies, Parenthesized(inequality));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(Context(body))));
    }
}

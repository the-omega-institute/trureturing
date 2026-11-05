using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.QGammaTuran;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2018qgamma");
    private const string Prefix = "D5/S3/Analytic/QGammaTuran/Result.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative Cauchy coefficient for a reciprocal q-gamma series.",
        H("The coefficient clause of Conjecture 1 is false"), Blocks(
            Describe.Lean(DescribeId.Create("qgamma-product"),
                DeclarationHandle.Create(Prefix + "qprod"),
                H("The q-Pochhammer infinite product"),
                StatementSource.FromAuthor(Disp(All("q", Seq(R, Sp), All("a", Seq(R, Sp),
                    Eqn(new Formula.Apply(Seq(Operatorname, Grp(V("qprod")), Sp), [V("q"), V("a")]),
                        Product("j", Sub(D(1), Mul(V("a"), Pow(V("q"), V("j")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product with parameter a has factors 1−aqʲ. It supplies the normalized series in FunctionResult."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reciprocal-qgamma"),
                DeclarationHandle.Create(Prefix + "rqgamma"),
                H("Reciprocal q-gamma by its infinite product"),
                StatementSource.FromAuthor(Disp(ReciprocalFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (6), page 4 of arXiv:1702.03788v1: “The q-gamma function is defined by Γq(z) = (1 − q)^(1−z) (q; q)∞/(q^z; q)∞ (6) for |q| < 1 and all complex z such that q^(z+k) ≠ 1 for k ∈ N₀.” The preceding definition is “(a; q)∞ = lim n→∞ (a; q)n”, with (a; q)n the product of 1−aq^k for k from zero to n−1. For real 0<q<1 the numerator in rqgamma is (q^x;q)∞ and its denominator is (q;q)∞ times (1−q)^(1−x). Thus rqgamma is the reciprocal of equation (6) wherever Γq is finite. For 0<q<1 the denominator is nonzero. The numerator vanishes exactly when x is a nonpositive integer: a factor is zero precisely when x+j=0 for some natural j. This gives the reciprocal extension by zero used for the series coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qgamma-turan-coefficient"),
                DeclarationHandle.Create(Prefix + "qturanCoeff"),
                H("The exact Cauchy coefficient"),
                StatementSource.FromAuthor(Disp(CoefficientFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 3 uses g(µ;x)=∑ₙ₌₀∞ gₙxⁿ/Γq(µ+n) and ∆g(α,β;x)=g(µ+α;x)g(µ+β;x)−g(µ;x)g(µ+α+β;x). The coefficient of x^m in these two Cauchy products is exactly qturanCoeff: k runs from zero to m and the second index is m−k. The subtraction order is unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qgamma-coefficient-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The coefficient assertion for positive real shifts"),
                StatementSource.FromAuthor(Disp(Eqn(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 3, page 11 of arXiv:1702.03788v1: “For a real sequence {gₙ}ₙ≥₀ and fixed 0 < q < 1 define g(µ; x) = ∑ₙ₌₀∞ gₙxⁿ/Γq(µ + n). (16) Suppose {gₙ}∞ₙ₌₀ is doubly positive. Then (16) has a positive radius of convergence Rg and the generalized Turánian ∆g(α, β; x) = g(µ + α; x)g(µ + β; x) − g(µ; x)g(µ + α + β; x) is positive for 0 < x < Rg if α ∈ N, β > 0 and µ ≥ max(−β, −1). If, in addition, α ≤ β + 1, then ∆g(α, β; x) has positive power series coefficients at all powers of x.”")),
                    Paragraph(Text("Conjecture 1, page 12: “All conclusions of Theorem 3 are valid for all α > 0, while conditions on other parameters remain intact. In particular, µ → g(µ; x) is log-concave for each fixed 0 < x < Rg.” The claim retains α≤β+1 and asks only for the coefficient conclusion. A counterexample with that restriction refutes the coefficient conclusion under either reading of the preceding discussion about removing restrictions.")),
                    Paragraph(Text("The definition on page 3 states: “A sequence f : N₀ → R₊ is PF₂ (Pólya frequency sub two) or doubly positive if it is nontrivial, log-concave, fₖ² ≥ fₖ₋₁fₖ₊₁, k ∈ N, and has no internal zeros. The last claim means that fN = 0 implies either fN+i = 0 for all i ∈ N₀ or fN−i = 0 for i = 0, . . . , N.” These are exactly the nontriviality, nonnegativity, log-concavity and no-internal-zeros conditions of the reused D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq. Its frozen theorem admissible_one supplies the constant sequence gₙ=1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qgamma-coefficient-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A negative coefficient of degree two"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take gₙ=1, r=99/100, q=r^10, µ=−7/10 and α=β=7/10, and take m=2. All parameter inequalities in claim hold. The product recurrence gives rqgamma(q,x)=[x]q rqgamma(q,x+1), where [x]q=(1−q^x)/(1−q); in particular rqgamma(q,0)=0 and rqgamma(q,1)=rqgamma(q,2)=1.")),
                    Paragraph(Text("The coefficient is 1−P C, with P=rqgamma(q,3/10)rqgamma(q,7/10) and C=[−7/10]q/([7/10]q[17/10]q)+1/[7/10]q+1/[3/10]q. The identities q^(3/10)=r^3 and q^(7/10)=r^7 reduce the required comparisons to rational powers of r. Finite partial products give upper bounds on each infinite product; multiplying a partial product by 1−a q^N/(1−q) gives a lower bound for (a;q)∞. With N=58 and outward rational enclosures at denominator 10^20, the lower bounds for (r^3;q)∞ and (r^7;q)∞ are respectively 4119/100000000000 and 23803/100000000000, while (q;q)∞ is at most 63655/100000000000. The rational q-number expression C exceeds 397/100. These bounds imply P C>1, so the degree-two coefficient is negative.")),
                    Paragraph(Text("The conclusion concerns the coefficient clause. The function-positivity and parameter-log-concavity conclusions are not asserted here. The integer-shift theorem is unaffected because α=7/10 is not an integer."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kalmykov-karp-2018-qgamma-turanian-coefficients"),
                    ResolutionKind.Refuted)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        return new Formula.Apply(Seq(Operatorname, Grp([.. parts])), [.. args]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Positive(Formula value) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, value);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Product(string name, Formula body) => Seq(
        new Formula.Subscript(Seq(Prod, Apos), Seq(V(name), Colon, Sp, N)), Sp, Parenthesized(body));
    private static Formula Scalars(Formula body) =>
        All("mu", R, All("alpha", R, All("beta", R, body)));
    private static Formula Coefficient(Formula degree) =>
        Call("qturanCoeff", V("q"), V("g"), V("mu"), V("alpha"), V("beta"), degree);
    private static Formula Reciprocal(Formula point) => Call("rqgamma", V("q"), point);
    private static Formula ReciprocalFormula()
    {
        var numerator = Product("j", Sub(D(1), Pow(V("q"), Add(V("x"), V("j")))));
        var denominator = Mul(Product("j", Sub(D(1), Pow(V("q"), Add(V("j"), D(1))))),
            Pow(Sub(D(1), V("q")), Sub(D(1), V("x"))));
        return All("q", R, All("x", R,
            Eqn(Reciprocal(V("x")), new Formula.Fraction(numerator, denominator))));
    }
    private static Formula CoefficientFormula()
    {
        var k = V("k");
        var other = Sub(V("m"), k);
        var first = Mul(Reciprocal(Add(Add(k, V("mu")), V("alpha"))),
            Reciprocal(Add(Add(other, V("mu")), V("beta"))));
        var second = Mul(Reciprocal(Add(k, V("mu"))),
            Reciprocal(Add(Add(Add(other, V("mu")), V("alpha")), V("beta"))));
        var summand = Mul(Mul(new Formula.Apply(V("g"), [k]),
            new Formula.Apply(V("g"), [other])), Parenthesized(Sub(first, second)));
        var sum = Seq(new Formula.Subscript(Sum, Seq(k, InMacro, Sp,
            Call("Finset.range", Add(V("m"), D(1))))), Sp, summand);
        return All("q", R, All("g", new Formula.TypeArrow(N, R), Scalars(All("m", N,
            Eqn(Coefficient(V("m")), sum)))));
    }
    private static Formula ClaimBody()
    {
        var coefficient = All("m", N, Positive(Coefficient(V("m"))));
        var parameters = Scalars(Imp(Positive(V("alpha")), Imp(Positive(V("beta")),
            Imp(Leq(Call("max", new Formula.Negate(V("beta")), new Formula.Negate(D(1))), V("mu")),
                Imp(Leq(V("alpha"), Add(V("beta"), D(1))), coefficient)))));
        var sequence = All("g", new Formula.TypeArrow(N, R), Imp(
            Call("D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq", V("g")), parameters));
        return All("q", R, Imp(Positive(V("q")), Imp(
            new Formula.Relation(V("q"), FormulaRelationOperator.LessThan, D(1)), sequence)));
    }
}

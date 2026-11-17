using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class YinPolygammaMajorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/yin2022polygamma");
    private const string MajorizationQuotation =
        "Page 916: “Let α=(α₁,α₂,⋯,αₙ) and β=(β₁,β₂,⋯,βₙ)∈ℝⁿ. "
        + "A n-tuple α is said to strictly majorize β (in symbols α≻β) if "
        + "(α[1],α[2],⋯,α[n])≠(β[1],β[2],⋯,β[n]), "
        + "∑ᵢ₌₁ᵏ α[i]≥∑ᵢ₌₁ᵏ β[i] for 1≤k≤n−1, and ∑ᵢ₌₁ⁿ αᵢ=∑ᵢ₌₁ⁿ βᵢ "
        + "where α[1]≥α[2]≥⋯≥α[n], β[1]≥β[2]≥⋯≥β[n] are rearrangements "
        + "of α and β in a descending order.” ";
    private const string Quotation =
        "Conjecture 4.1, p. 920: “For p,k>0 and every α₁,α₂,⋯αₙ,β₁,β₂,⋯βₙ∈ℕ such that "
        + "(α₁,α₂,⋯,αₙ)≺(β₁,β₂,⋯,βₙ), the function "
        + "Qα₁,α₂,⋯,αₙ;β₁,β₂,⋯,βₙ,p,k(x)="
        + "[ψₚ,ₖ⁽α₁⁾(x)⋯ψₚ,ₖ⁽αₙ⁾(x)]/[ψₚ,ₖ⁽β₁⁾(x)⋯ψₚ,ₖ⁽βₙ⁾(x)] "
        + "is decreasing on (0,∞) onto the interval "
        + "(((α₁−1)!⋯(αₙ−1)!)/((β₁−1)!⋯(βₙ−1)!),(α₁!⋯αₙ!)/(β₁!⋯βₙ!)).”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict finite-moment gap and equal endpoint limits refute finite polygamma majorization monotonicity.",
        H("Finite Polygamma Majorization Refutation"),
        Blocks(
            Entry("psi", "psi", "Finite digamma", PsiDefinition(),
                AssessedProvenance.FromLiterature(Source),
                "Equation (1.5), p. 916, defines ψₚ,ₖ(x) = (1/k) ln(pk) − ∑ⱼ₌₀ᵖ 1/(jk+x). "
                + "The index p is a positive integer and k and x are positive reals in the source domain; "
                + "the Lean function is total on all real arguments.", DescribeRole.Definition),
            Entry("polygamma", "polygamma", "Derivatives of the finite digamma", PolygammaDefinition(),
                AssessedProvenance.FromLiterature(Source),
                "The sentence before (1.5), p. 916, defines “ψₚ,ₖ⁽ᵐ⁾(x) = dᵐ/dxᵐ ψₚ,ₖ(x).” "
                + "Mathlib iteratedDeriv expresses this derivative. For positive order r its value is "
                + "(−1)ʳ⁺¹ r! times the sum of (jk+x)⁻ʳ⁻¹. The finite-sum sign printed in (1.6) "
                + "differs from differentiation of (1.5); the derivative definition is used here.", DescribeRole.Definition),
            Entry("strict-majorization", "StrictlyMajorized", "Strict majorization of the order tuples",
                MajorizationDefinition(), AssessedProvenance.FromLiterature(Source),
                MajorizationQuotation + "Here a≺b means that b strictly majorizes a. "
                + "The imported moreMixed gives the prefix inequalities and equal totals, and desc gives "
                + "the descending rearrangement. Natural orders are cast into the real carrier of these operations.",
                DescribeRole.Definition),
            Entry("quotient", "Q", "The multifactor quotient", QuotientDefinition(),
                AssessedProvenance.FromLiterature(Source),
                Quotation + " Fin n indexes the n factors from zero; "
                + "the source indexes them from one. Positive orders and positive x make every denominator factor nonzero.",
                DescribeRole.Definition),
            Entry("claim", "claim", "Conjecture 4.1", Seq(Call("claim"), Iff, Sp, Parenthesized(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                Quotation + " The formula below retains both weak decrease and equality of the entire image with the "
                + "open factorial interval. The parameters p and n and the orders are positive naturals; k is a positive real. "
                + "The letters a and b encode α and β. Natural subtraction at order minus one is protected by positivity.",
                DescribeRole.Definition),
            Entry("result", "result", "Refutation of Conjecture 4.1", new Formula.Not(Parenthesized(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                "For every p≥1, k>0, m≥2 and length l+2, take a constant tuple of order m and "
                + "a second tuple with first two orders m−1,m+1 and l remaining orders m. The second tuple "
                + "strictly majorizes the first. Cancelling nonzero common factors reduces Q to m/(m+1) "
                + "times the neighboring-moment quotient. The Gram identity gives a strictly positive dispersion "
                + "gap, so this quotient lies strictly between zero and m/(m+1) at every positive x. "
                + "Both endpoint limits equal m/(m+1), excluding weak monotonicity in either direction. "
                + "The final contradiction uses p=k=1, m=2 and l=1. This argument concerns finite truncations; "
                + "it asserts no conclusion for ordinary untruncated polygamma functions.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            declaration == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("yin-polygamma-majorization-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => FormulaDsl.Id(name);
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
        var op = Seq(Operatorname, Grp([.. parts]));
        return args.Length == 0 ? op : new Formula.Apply(op, [.. args]);
    }
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Seq(Call("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula RealCast(Formula a) => Parenthesized(Seq(Call("Nat.cast", a), Colon, Sp, R));
    private static Formula TupleType(Formula n) => new Formula.TypeArrow(Call("Fin", n), N);
    private static Formula Sum(Formula set, Formula body) =>
        Seq(FormulaDsl.Sum, Underscore, Grp(V("j"), InMacro, Sp, set), Sp, Parenthesized(body));
    private static Formula Product(Formula n, Formula body) =>
        Seq(Prod, Underscore, Grp(V("i"), Colon, Sp, Call("Fin", n)), Sp, Parenthesized(body));
    private static Formula CastTuple(Formula a, Formula n) =>
        Fn("i", Call("Fin", n), RealCast(App(a, V("i"))));
    private static Formula Geometry(string name, params Formula[] args) =>
        Call("D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing." + name, args);

    private static Formula PsiDefinition()
    {
        Formula p = V("p"), k = V("k"), x = V("x"), j = V("j");
        return All("p", N, All("k", R, All("x", R,
            Eqn(Call("psi", p, k, x), Sub(Mul(Div(D(1), k), Call("Real.log", Mul(RealCast(p), k))),
                Sum(Call("Finset.range", Add(p, D(1))), Div(D(1), Add(Mul(RealCast(j), k), x))))))));
    }
    private static Formula PolygammaDefinition() =>
        All("p", N, All("k", R, All("m", N, All("x", R,
            Eqn(Call("polygamma", V("p"), V("k"), V("m"), V("x")),
                Call("iteratedDeriv", V("m"), Call("psi", V("p"), V("k")), V("x")))))));
    private static Formula MajorizationDefinition()
    {
        Formula n = V("n"), a = V("a"), b = V("b");
        return All("n", N, All("a", TupleType(n), All("b", TupleType(n),
            Seq(Call("StrictlyMajorized", a, b), Iff, Sp, Parenthesized(And(
                Geometry("moreMixed", CastTuple(a, n), CastTuple(b, n)),
                Ne(Geometry("desc", CastTuple(a, n)), Geometry("desc", CastTuple(b, n)))))))));
    }
    private static Formula QuotientDefinition()
    {
        Formula n = V("n"), p = V("p"), k = V("k"), a = V("a"), b = V("b"), x = V("x");
        return All("n", N, All("p", N, All("k", R, All("a", TupleType(n), All("b", TupleType(n), All("x", R,
            Eqn(Call("Q", p, k, a, b, x), Div(
                Product(n, Call("polygamma", p, k, App(a, V("i")), x)),
                Product(n, Call("polygamma", p, k, App(b, V("i")), x))))))))));
    }
    private static Formula ClaimBody()
    {
        Formula p = V("p"), k = V("k"), n = V("n"), a = V("a"), b = V("b");
        Formula q = Call("Q", p, k, a, b), domain = Call("Set.Ioi", D(0));
        Formula low = Div(Product(n, RealCast(Call("Nat.factorial", Sub(App(a, V("i")), D(1))))),
            Product(n, RealCast(Call("Nat.factorial", Sub(App(b, V("i")), D(1))))));
        Formula high = Div(Product(n, RealCast(Call("Nat.factorial", App(a, V("i"))))),
            Product(n, RealCast(Call("Nat.factorial", App(b, V("i"))))));
        Formula conclusion = And(Call("AntitoneOn", q, domain),
            Eqn(Call("Set.image", q, domain), Call("Set.Ioo", low, high)));
        return All("p", N, Imp(LtTo(D(0), p), All("k", R, Imp(LtTo(D(0), k),
            All("n", N, Imp(LtTo(D(0), n), All("a", TupleType(n), All("b", TupleType(n),
                Imp(All("i", Call("Fin", n), LtTo(D(0), App(a, V("i")))),
                    Imp(All("i", Call("Fin", n), LtTo(D(0), App(b, V("i")))),
                        Imp(Call("StrictlyMajorized", a, b), conclusion)))))))))));
    }
}

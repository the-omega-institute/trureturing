using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace;

internal sealed class CyclicSignTraceBooleanCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.";
    private static readonly LibraryNoteRef SourceNote =
        LibraryNoteRef.Create("D5/L/Fourier/ricardorr2026mo512655");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Boolean coefficient extraction supplies the exact top-degree equations used by the rank assembly.",
        H("Boolean coefficients and top-degree constraints"),
        Blocks(
            Node("booleanMonomial", "Squarefree Boolean monomials", StatementSource.WithoutFormula(),
                "For a finite set s of actual cyclic coordinates, booleanMonomial(s,z) is the product of z_i over i in s. Repeated cyclic coordinates are represented only once; the empty monomial is one.", DescribeRole.Definition),
            Node("indicatorWord", "Indicator words", StatementSource.WithoutFormula(),
                "The word indicatorWord(s) is one at coordinates in s and zero elsewhere.", DescribeRole.Definition),
            Node("booleanCoeff", "Coefficients from actual function values", StatementSource.WithoutFormula(),
                "The coefficient of a Boolean function f at s is the sum in ZMod 2 of f(indicatorWord(t)) over every subset t of s. Thus equal actual functions have equal coefficients. Subset cancellation proves that extraction applied to the monomial at t is one exactly when s=t and zero otherwise; this establishes uniqueness for finite sums of squarefree monomials without assuming injectivity of polynomial evaluation.", DescribeRole.Definition),
            Node("coeff_monomial", "Coefficient extraction on a monomial", StatementSource.WithoutFormula(),
                "Extraction of a squarefree Boolean monomial at a finite coordinate set is the equality indicator for the two sets. This is the subset-cancellation fact used by every coefficient expansion below.", DescribeRole.Lemma),
            Node("coeff_add", "Coefficient extraction is additive", StatementSource.WithoutFormula(),
                "Boolean coefficient extraction of a pointwise sum is the sum of the extracted coefficients.", DescribeRole.Lemma),
            Node("coeff_sum", "Coefficient extraction commutes with finite sums", StatementSource.WithoutFormula(),
                "Boolean coefficient extraction commutes with a finite indexed sum of Boolean functions.", DescribeRole.Lemma),
            Node("coeff_mul", "Scalar multiplication under coefficient extraction", StatementSource.WithoutFormula(),
                "Multiplying a Boolean function by a binary scalar multiplies its extracted coefficient by the same scalar.", DescribeRole.Lemma),
            Node("coeff_constant", "Constant coefficient extraction", StatementSource.WithoutFormula(),
                "For every binary scalar a and every nonempty finite coordinate set s, the coefficient at s of the constant function with value a is zero.", DescribeRole.Lemma),
            Node("prefixVariables", "Cyclic prefix variable sets", StatementSource.WithoutFormula(),
                "The finite set prefixVariables(i,r) is the image of t=0,...,r-1 under t ↦ i+2t+1 in the actual cyclic index type.", DescribeRole.Definition),
            Node("monomial_insert", "Inserting an endpoint into a monomial", StatementSource.WithoutFormula(),
                "The Boolean monomial on a finite set with one endpoint inserted factors as the endpoint value times the monomial on the original set, with duplicate coordinates handled by binary idempotence.", DescribeRole.Lemma),
            Node("shifted_inverse_expansion", "Expansion of the shifted inverse component", StatementSource.WithoutFormula(),
                "After translating the inverse input by the all-one word, the inverse component expands into the prefix monomials and their endpoint insertions with the original mask coefficients.", DescribeRole.Lemma),
            Node("inverse_component_boolean_coefficient", "Exact coefficients of the shifted inverse component", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.BooleanCoefficientFormula()),
                "For every m, mask b and finite cyclic-coordinate set s, extract the coefficient of z ↦ inverseComponent(m,b)(1+z). Each inverse term contributes the prefix monomial and the prefix with its endpoint i+2r inserted, weighted by b_i. Equality of finite sets decides whether each contributes at s. This statement includes all masks and length one, with no distinct-index premise.", DescribeRole.Theorem),
            Paragraph(Text("Binary idempotence identifies a product over repeated coordinates with its squarefree monomial. After y=1+z the alternating prefix becomes the monomial on prefixVariables(i,r), and its endpoint factor is 1+z_(i+2r). The coefficient formula follows by linearity of extraction and the subset-cancellation identity. No Boolean normal-form uniqueness or coefficient vanishing is assumed.")),
            Node("monomialDerivativeCoeff", "Exact monomial derivative coefficients", StatementSource.WithoutFormula(),
                "At variable sets t,s and direction u, this is the product of u on t minus s when s is a subset of t, plus one when s=t; absent contributions are zero. Product expansion and coefficient extraction prove that this is the coefficient at s of z ↦ booleanMonomial(t,z+u)+booleanMonomial(t,z).", DescribeRole.Definition),
            Node("inverse_component_derivative_coefficients", "Necessary coefficient equations for a constant inverse derivative", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.DerivativeCoefficientFormula()),
                "For every m, b,u and nonempty finite set s, if the derivative of the actual inverse component in direction u is constant on all words, the displayed sum of its monomial derivative coefficients is zero. The proof translates by the all-one word and extracts the coefficient from actual functions. It assumes neither a degree argument nor the intended mask classification.", DescribeRole.Theorem),
            Node("topVariables", "Highest-degree cyclic variable sets", StatementSource.WithoutFormula(),
                "The set topVariables(m,i) is prefixVariables(i,m) with coordinate i+2m inserted. It has m+1 elements. Its coordinate sum has slope m+1 as a function of i; multiplication by two in the odd cycle inverts that slope, so the sets for distinct i are distinct.", DescribeRole.Definition),
            Node("prefix_index_injective", "The indices within a prefix are distinct", StatementSource.WithoutFormula(),
                "For r at most m and a fixed starting coordinate i on the cycle of length 2m+1, the map t ↦ i+2t+1 is injective on t=0,...,r-1.", DescribeRole.Lemma),
            Node("prefix_card", "Prefix cardinality", StatementSource.WithoutFormula(),
                "A prefix of length r at an odd cycle has exactly r coordinates whenever r is at most m.", DescribeRole.Lemma),
            Node("endpoint_not_prefix", "The endpoint is outside its prefix", StatementSource.WithoutFormula(),
                "For r at most m, the endpoint coordinate i+2r is not already in prefixVariables(i,r).", DescribeRole.Lemma),
            Node("top_card", "Top-variable set cardinality", StatementSource.WithoutFormula(),
                "Each topVariables(m,i) set has exactly m+1 coordinates.", DescribeRole.Lemma),
            Node("inverse_component_top_coefficient", "Highest-degree coefficients recover every mask bit", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.TopCoefficientFormula()),
                "For every m, b and cyclic coordinate i, the coefficient of the shifted inverse component at topVariables(m,i) is exactly b_i. Cardinality excludes every shorter prefix and endpoint term; injectivity of the highest-degree variable sets leaves exactly the term indexed by i. Length one and zero masks are included.", DescribeRole.Theorem),
            Node("inverse_component_top_derivative", "The degree-m derivative equation", StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.TopDerivativeFormula()),
                "For every positive m and constant derivative direction u of the inverse component, and every finite coordinate set s of cardinality m, the sum over i of b_i times the product of u on topVariables(m,i) minus s, with zero contribution unless s is a subset, vanishes. A derivative of a monomial of degree at most m has zero degree-m coefficient; hence only the degree-(m+1) endpoint terms survive. The statement includes m=1 but does not claim the subsequent overlap classification.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string name, string title, StatementSource statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cyclic-sign-trace-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), statement, AssessedProvenance.FromRepo(SourceNote),
            Blocks(Paragraph(Text(prose))), role);
}

internal static class CyclicSignTraceScribeFormulas
{
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula All(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Some(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.And, Grp(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Implies, Grp(b));
    private static Formula Bin(Formula a, FormulaBinaryOperator op, Formula b) => new Formula.Binary(Grp(a), op, Grp(b));
    private static Formula Plus(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Add, b);
    private static Formula Times(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Word(Formula n) => Call("Word", n);
    private static Formula Sum(string x, Formula t, Formula body) => Seq(F.Sum, Underscore, Grp(F.Id(x), Sp, InMacro, Sp, t), Sp, body);
    private static Formula OddLength(Formula m) => Plus(Times(D(2), m), D(1));

    internal static Formula InverseFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"),
            And(All("x", w, Eq(Call("inverse", m, Call("chi", x)), x)),
                All("y", w, Eq(Call("chi", Call("inverse", m, y)), y)))));
    }

    internal static Formula InversionFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), y = F.Id("y"), a = F.Id("a"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), All("y", w,
                Eq(Sum("a", w, Times(Call("walsh", f, a), Call("sign", Call("dot", a, y)))),
                    Times(Call("card", w), Call("sign", Call("f", y)))))))));
    }

    internal static Formula NonemptyFormula()
    {
        Formula n = F.Id("n"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), Some("a", w,
                Rel(Call("walsh", F.Id("f"), F.Id("a")), FormulaRelationOperator.NotEqual, D(0)))))));
    }

    internal static Formula PhaseNonemptyFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, Some("a", w,
            Rel(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                FormulaRelationOperator.NotEqual, D(0))))));
    }

    internal static Formula PhaseFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, All("a", w,
            Eq(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                Call("walsh", Call("inverseComponent", m, b), a))))));
    }

    internal static Formula WalshDerivativeFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), u = F.Id("u"), c = F.Id("c"),
            y = F.Id("y"), a = F.Id("a"), w = Word(n), bit = Call("ZMod", D(2));
        Formula derivative = All("y", w,
            Eq(Plus(Call("f", Plus(y, u)), Call("f", y)), c));
        Formula support = All("a", w,
            Imp(new Formula.Relation(Call("walsh", f, a), FormulaRelationOperator.NotEqual, D(0)),
                Eq(Call("dot", a, u), c)));
        return Disp(All("n", Named("Nat"),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
                All("f", Arrow(w, bit), All("u", w, All("c", bit,
                    new Formula.Logic(Grp(derivative), FormulaLogicOperator.Iff,
                        Grp(support))))))));
    }

    internal static Formula AffineDualityFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), u = F.Id("u"), c = F.Id("c"), y = F.Id("y"),
            w = Word(n), bit = Call("ZMod", D(2));
        Formula derivative = Some("c", bit,
            All("y", w, Eq(Plus(Call("f", Plus(y, u)), Call("f", y)), c)));
        Formula membership = Call("mem", u, Call("constantDerivativeSubmodule", f));
        Formula finrankD = Call("finrank", bit, Call("constantDerivativeSubmodule", f));
        Formula finrankA = Call("finrank", bit, Call("walshSupportDirection", f));
        Formula finrankV = Call("finrank", bit, w);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, bit),
                And(All("u", w,
                        new Formula.Logic(Grp(membership), FormulaLogicOperator.Iff,
                            Grp(derivative))),
                    Eq(Plus(finrankD, finrankA), finrankV))))));
    }

    internal static Formula TracePhaseFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("b", w, All("a", w,
                Eq(Call("sourceTrace", b, a),
                    Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x)))))))))));
    }

    internal static Formula BooleanCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), s = F.Id("s"), i = F.Id("i"), r = F.Id("r"),
            n = OddLength(m), p = Call("prefixVariables", i, r);
        Formula delta(Formula t) => Call("ite", Eq(s, t), D(1), D(0));
        Formula endpoint = Plus(i, Times(D(2), r));
        Formula rhs = Sum("i", Call("ZMod", n), Sum("r", Call("range", Plus(m, D(1))),
            Times(Call("b", i), Plus(delta(p), delta(Call("insert", endpoint, p))))));
        Formula shifted = Seq(Grp(F.Id("z"), F.Colon, Word(n)), F.Mapsto,
            Call("inverseComponent", m, b, Plus(D(1), F.Id("z"))));
        return Disp(All("m", Named("Nat"), All("b", Word(n),
            All("s", Call("Finset", Call("ZMod", n)), Eq(Call("booleanCoeff", shifted, s), rhs)))));
    }

    internal static Formula DerivativeCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), u = F.Id("u"), s = F.Id("s"),
            i = F.Id("i"), r = F.Id("r"), y = F.Id("y"), n = OddLength(m), p = Call("prefixVariables", i, r);
        Formula constant = Some("c", Call("ZMod", D(2)), All("y", Word(n),
            Eq(Plus(Call("inverseComponent", m, b, Plus(y, u)), Call("inverseComponent", m, b, y)), F.Id("c"))));
        Formula rhs = Sum("i", Call("ZMod", n), Sum("r", Call("range", Plus(m, D(1))),
            Times(Call("b", i), Plus(Call("monomialDerivativeCoeff", p, s, u),
                Call("monomialDerivativeCoeff", Call("insert", Plus(i, Times(D(2), r)), p), s, u)))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), All("u", Word(n),
            Imp(constant, All("s", Call("Finset", Call("ZMod", n)),
                Imp(Call("Nonempty", s), Eq(rhs, D(0)))))))));
    }

    internal static Formula TopCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), i = F.Id("i"), n = OddLength(m);
        Formula shifted = Seq(Grp(F.Id("z"), F.Colon, Word(n)), F.Mapsto,
            Call("inverseComponent", m, b, Plus(D(1), F.Id("z"))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), All("i", Call("ZMod", n),
            Eq(Call("booleanCoeff", shifted, Call("topVariables", m, i)), Call("b", i))))));
    }

    internal static Formula TopDerivativeFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), u = F.Id("u"), s = F.Id("s"),
            i = F.Id("i"), n = OddLength(m), t = Call("topVariables", m, i);
        Formula summand = Times(Call("b", i), Call("ite", Call("subset", s, t),
            Call("booleanMonomial", Call("sdiff", t, s), u), D(0)));
        Formula sets = All("s", Call("Finset", Call("ZMod", n)),
            Imp(Eq(Call("card", s), m), Eq(Sum("i", Call("ZMod", n), summand), D(0))));
        Formula directions = All("b", Word(n), All("u", Word(n), Imp(
            Call("mem", u, Call("constantDerivativeSubmodule", Call("inverseComponent", m, b))), sets)));
        return Disp(All("m", Named("Nat"),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, m), directions)));
    }

    internal static Formula SupportDimensionFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), n = OddLength(m), bit = Call("ZMod", D(2));
        Formula rank = Call("finrank", bit, Call("direction", Call("affineSpan", bit, Call("traceSupport", b))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), Imp(
            Rel(b, FormulaRelationOperator.NotEqual, D(0)),
            Rel(Times(D(2), m), FormulaRelationOperator.LessThanOrEqual, rank)))));
    }
}

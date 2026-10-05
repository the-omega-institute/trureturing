using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class XYPaddedGinibreRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/abdesselam2022nonabelian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The XY model violates a padded general Ginibre inequality on a five-cycle.",
        H("The XY model violates a padded Ginibre inequality"),
        Blocks(
            Node("measure", "The free O(2) probability measure", MeasureFormula(),
                """Page 2: "The free measure μ is the product of copies of the unique O(N)-invariant Borel probability measure on the sphere Sᴺ⁻¹." Here N = 2. The rotation-invariant probability measure on S¹ is the image of normalized Haar measure on angles under θ ↦ (cos θ, sin θ). The carrier Real.Angle is Mathlib's AddCircle (2 * Real.pi), and freeMeasure p is the product measure on Fin p → Real.Angle. AddCircle.haarAddCircle has total mass one; the displayed argument is its implicit period 2 * Real.pi, and its positivity proof is Real.two_pi_pos. Function.const supplies the same angle measure at every site.""",
                "freeMeasure"),
            Node("spin", "Unit spins in angle coordinates", SpinFormula(),
                """Page 2: "Each spin σᵢ is a column vector (σᵢ,₁,…,σᵢ,ᴺ)ᵀ in Sᴺ⁻¹, i.e., which satisfies Σ_{ℓ=1}ᴺ σᵢ,ℓ² = 1." With N = 2 the vector spin θ has coordinates cos θ and sin θ, in this order. The displayed vector is the Lean vector notation ![Real.Angle.cos θ, Real.Angle.sin θ], a function Fin 2 → ℝ. The identity cos² θ + sin² θ = 1 makes it a unit spin.""",
                "spin"),
            Node("observable", "Pair observables", ObservableFormula(),
                """Page 2: "The basic observables are the inner products σᵢ·σᵢ′ := Σ_{ℓ=1}ᴺ σᵢ,ℓ σᵢ′,ℓ, with 1 ≤ i < i′ ≤ p." Fin indices are zero-based. All pairs are represented by the subtype {e : Fin p × Fin p // e.1 < e.2}; val is the existing Subtype.val projection. Mathlib dotProduct is the sum of the two products of spin coordinates.""",
                "observable"),
            Node("monomial", "Observable monomials", MonomialFormula(),
                "Page 2: \"we will write 𝒪(x)^a or just 𝒪^a for the monomial 𝒪₁(x)^a₁ ⋯ 𝒪ₙ(x)^aₙ in the basic observables.\" The natural multiindex is called u in monomial. The product ranges over every pair i < j, including pairs whose exponent is zero. Both x and u retain the same pair and site carriers as observable.",
                "monomial"),
            Node("parity", "The endpoint parity homomorphism", ParityFormula(),
                """Page 5: "In the case of the O(N) model as described above, we take L = p and for j corresponding to a pair of vertices (i,i′), with 1 ≤ i < i′ ≤ p, we define ρ(eⱼ) as the vector with all components equal to 0 except the i'-th and i′-th components which are set equal to 1." The integer multiindex a contributes a(e) modulo two at both endpoints of each pair e. The displayed evaluation specifies parity p as an additive homomorphism from integer pair-indices to Fin p → ZMod 2; ite is the ordinary conditional expression.""",
                "parity"),
            Node("pgg", "The padded general Ginibre functional", PggFormula(),
                """Page 6: "We will say that the system (X, μ, 𝒪, L, ρ) satisfies the PGG collection of inequalities iff ∀ m ≥ 0, ∀ V ∈ ℕᵐˣⁿ, ∀ (ε₁,…,εₘ) ∈ {−1,1}ᵐ, and all even u ∈ ℕⁿ we have" the duplicated integral at least zero. The displayed definition is that integral before the inequality. Rows V i and padding u are natural pair-indices. The integral is over two independent configurations using Measure.prod (freeMeasure p) (freeMeasure p); Prod.fst and Prod.snd project the two configurations. The finite product ranges over Fin m and is one when m = 0.""",
                "pgg"),
            Node("claim", "Problem 2: the XY-PGG assertion", ClaimFormula(),
                """Page 14: "For the XY model, or O(2) model, the GG inequalities were proved by Ginibre [18]. What about the padded generalizations given by the PGG inequalities?" The displayed claim asks for the PGG collection on every p ≥ 1 sites. It retains every quantifier from p. 6: m is any natural number, V has natural entries on all pairs, every real ε i is −1 or 1, and u is any even natural multiindex. Page 5: "We will say that a is even iff ρ(a) = 0." The inline condition casts u coordinatewise to integers before applying parity p; zero is the zero function Fin p → ZMod 2. No condition that the sum of the rows of V be even is imposed in this definition of the PGG collection. The angle measure convention is stated above.""",
                "claim"),
            Describe.Lean(
                DescribeId.Create("xy-pgg-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The XY-PGG assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take p = 5 and the five pairs (0,1), (1,2), (2,3), (3,4), (0,4). Let u be their indicator, m = 2, both rows V i = u, and both signs ε i = −1. Each vertex is incident to two chosen pairs, so u is even. Set Z(x) to the product of the five pair observables. Fourier orthogonality on each angle forces every surviving edge frequency to be constant around the cycle. Applying this to the first three powers gives M₁ = E[Z] = 1/16, M₂ = E[Z²] = 17/512 and M₃ = E[Z³] = 61/4096. The duplicated functional is E[Z(x)Z(y)(Z(x) − Z(y))²] = 2(M₁M₃ − M₂²) = −45/131072 < 0. The square factor is nonnegative, but the padding product Z(x)Z(y) can be negative; the exact moments show that its negative contribution prevails."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration) => Describe.Lean(
            DescribeId.Create("xy-pgg-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula AngleCall(string name, Formula theta) =>
        new Formula.Apply(Seq(Qualified("Real", "Angle"), Dot, Named(name)), [theta]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, v, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula EqTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Set(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula FinOf(Formula p) => Call("Fin", p);
    private static Formula Angles(Formula p) => Arrow(FinOf(p), Qualified("Real", "Angle"));
    private static Formula Indices(Formula p, Formula range) => Arrow(Pairs(p), range);
    private static Formula Rows(Formula m, Formula p) => Arrow(FinOf(m), Indices(p, Set("N")));
    private static Formula PairProduct(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Endpoint(Formula e, string side) => QualifiedCall("Prod", side, Call("val", e));
    private static Formula Pairs(Formula p)
    {
        Formula e = F.Id("e");
        return Seq(OpenBrace, e, Colon, PairProduct(FinOf(p), FinOf(p)), Mid,
            Rel(QualifiedCall("Prod", "fst", e), FormulaRelationOperator.LessThan,
                QualifiedCall("Prod", "snd", e)), CloseBrace);
    }
    private static Formula Indexed(Formula op, Formula v, Formula type, Formula body) =>
        Seq(op, Underscore, Grp(v, Colon, type), Sp, body);

    private static Formula MeasureFormula()
    {
        Formula p = F.Id("p");
        Formula haar = QualifiedCall("AddCircle", "haarAddCircle", Mul(D(2), Qualified("Real", "pi")));
        Formula family = QualifiedCall("Function", "const", FinOf(p), haar);
        return Disp(All(p, Set("N"), EqTo(Call("freeMeasure", p), QualifiedCall("Measure", "pi", family))));
    }
    private static Formula SpinFormula()
    {
        Formula theta = Theta;
        Formula vector = Seq(OpenBracket, AngleCall("cos", theta), Comma,
            AngleCall("sin", theta), CloseBracket);
        return Disp(All(theta, Qualified("Real", "Angle"), EqTo(Call("spin", theta), vector)));
    }
    private static Formula ObservableFormula()
    {
        Formula p = F.Id("p"), x = F.Id("x"), e = F.Id("e");
        Formula value = Call("dotProduct", Call("spin", App(x, Endpoint(e, "fst"))),
            Call("spin", App(x, Endpoint(e, "snd"))));
        return Disp(All(p, Set("N"), All(x, Angles(p), All(e, Pairs(p), EqTo(Call("observable", x, e), value)))));
    }
    private static Formula MonomialFormula()
    {
        Formula p = F.Id("p"), u = F.Id("u"), x = F.Id("x"), e = F.Id("e");
        Formula value = Indexed(Prod, e, Pairs(p), new Formula.Power(Call("observable", x, e), App(u, e)));
        return Disp(All(p, Set("N"), All(u, Indices(p, Set("N")), All(x, Angles(p),
            EqTo(Call("monomial", u, x), value)))));
    }
    private static Formula ParityFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), i = F.Id("i"), e = F.Id("e");
        Formula coefficient = Seq(Parenthesized(App(a, e)), Colon, Call("ZMod", D(2)));
        Formula Contribution(string side) => Call("ite", EqTo(Endpoint(e, side), i), coefficient, D(0));
        Formula value = Indexed(Sum, e, Pairs(p), Parenthesized(Add(Contribution("fst"), Contribution("snd"))));
        return Disp(All(p, Set("N"), All(a, Indices(p, Set("Z")), All(i, FinOf(p),
            EqTo(App(Call("parity", p), a, i), value)))));
    }
    private static Formula PggFormula()
    {
        Formula p = F.Id("p"), m = F.Id("m"), v = F.Id("V"), u = F.Id("u"), xy = F.Id("xy"), i = F.Id("i");
        Formula x = QualifiedCall("Prod", "fst", xy), y = QualifiedCall("Prod", "snd", xy);
        Formula factors = Indexed(Prod, i, FinOf(m), Parenthesized(Add(Call("monomial", App(v, i), x),
            Mul(App(Varepsilon, i), Call("monomial", App(v, i), y)))));
        Formula integrand = Mul(Mul(Call("monomial", u, x), Call("monomial", u, y)), Parenthesized(factors));
        Formula measure = QualifiedCall("Measure", "prod", Call("freeMeasure", p), Call("freeMeasure", p));
        Formula integral = Seq(Indexed(Int, xy, PairProduct(Parenthesized(Angles(p)), Parenthesized(Angles(p))),
            integrand), Sp, Named("d"), Parenthesized(measure));
        return Disp(All(p, Set("N"), All(m, Set("N"), All(v, Rows(m, p),
            All(Varepsilon, Arrow(FinOf(m), Set("R")), All(u, Indices(p, Set("N")),
                EqTo(Call("pgg", v, Varepsilon, u), integral)))))));
    }
    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p"), m = F.Id("m"), v = F.Id("V"), u = F.Id("u"), i = F.Id("i"), e = F.Id("e");
        Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
        Formula signs = All(i, FinOf(m), Logic(EqTo(App(Varepsilon, i), new Formula.Negate(D(1))),
            FormulaLogicOperator.Or, EqTo(App(Varepsilon, i), D(1))));
        Formula conclusion = Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Call("pgg", v, Varepsilon, u));
        Formula cast = Seq(e, Colon, Pairs(p), Mapsto, Seq(Parenthesized(App(u, e)), Colon, Set("Z")));
        Formula rows = All(m, Set("N"), All(v, Rows(m, p), All(Varepsilon, Arrow(FinOf(m), Set("R")),
            All(u, Indices(p, Set("N")), Imp(signs, Imp(EqTo(App(Call("parity", p), cast), D(0)), conclusion))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All(p, Set("N"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, p), rows))));
    }
}

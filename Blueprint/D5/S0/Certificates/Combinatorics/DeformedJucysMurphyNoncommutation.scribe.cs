using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics;

internal sealed class DeformedJucysMurphyNoncommutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/coulter2025weingarten");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coulter and Do's b-deformed Jucys--Murphy operators fail to commute on the cyclic orbit X(6). The word J_6 J_6 J_5 J_4 J_3 applied to the identity pair partition gives unequal coefficients after J_2 J_4 and J_4 J_2.",
        H("Noncommuting deformed Jucys--Murphy operators on the cyclic orbit"),
        Blocks(
            Node("pairs", "Pair partitions", PairFormula(),
                "A pair partition is encoded by its fixed-point-free involutive partner map. Its two-element orbits are its unordered pairs. Fin(2k) uses labels 0 through 2k-1, shifted down by one from the paper's labels 1 through 2k. The displayed set is a subtype. Type in the formulas permits an arbitrary Lean universe.", "P", true),
            Node("identity", "Consecutive identity pairs", IdentityFormula(),
                "The identity pair partition is (1 2 | 3 4 | ... | 2k-1 2k) in the paper's labels. Here val extracts the partner map from a pair partition, or the natural-number label from a Fin element, according to its argument. The functions natSub and mod denote natural-number subtraction and remainder; natSub is truncated at zero. ite(c,t,f) returns t when c holds and f otherwise.", "e", true),
            Node("action", "Transposition action", ActionFormula(),
                "Page 8: \"the pair {a, b} appears in the pair partition m if and only if the pair {σ(a), σ(b)} appears in the pair partition σ · m\". Relabelling by the transposition swapping a and c is conjugation of the partner map. swap(a,c) denotes the involutive permutation of Fin(2k).", "act", true),
            Node("walk", "Alternating walk", WalkFormula(),
                "Starting at x, the walk first follows an identity edge, then a matching edge, and repeats these two edge colours. The recurrence uses the natural-number remainder modulo two.", "walk", false),
            Node("charge", "Charge from the cycle maximum", ChargeFormula(),
                "Definition 4.1, page 21: \"To each vertex v ∈ Γ(m), assign a charge q(v) ∈ {+, −} such that the vertex with the largest label in each cycle is assigned + and such that each edge in Γ(m) is incident to one vertex with positive change and one vertex with negative charge.\" The walk implementation records the first occurrence of the maximum in its first 2k positions. A strict increase replaces the stored pair; ties retain it. true denotes positive charge, beq is Boolean equality, range(N) is [0,...,N-1], and foldl applies its update in this order. fst and snd project a pair. An alternating walk of an even component visits that component and repeats with even period. The maximum therefore has positive charge and both edge colours reverse charge. This interpretation of the algorithm is mathematical exposition, rather than an additional theorem asserted here.", "charge", true),
            Node("weight", "Transposition weight on the output matching", WeightFormula(),
                "Definition 4.1, page 21: \"Set ω^(b)(m,n) = 1 if q(i) = q(j) and set ω^(b)(m,n) = b if q(i) ≠ q(j).\" weight(b,p,a,c) is this rule restricted to the specified transposition (a c), with p as the first argument and act(a,c,p) as the second. The paper establishes independence of the transposition used. Only transposition-related pairs enter J, so the other cases of the full weight function are unnecessary here.", "weight", true),
            Node("operator", "Coefficient form of the deformed operators", OperatorFormula(),
                "Definition 5.1, page 33: \"For k a positive integer, let 𝒱ₖ = ℂ(b)[𝒫ₖ] be the vector space with basis the set of pair partitions of {1, 2, …, 2k}. Define the b-deformed Jucys–Murphy operators 𝒥₁, 𝒥₂, …, 𝒥ₖ: 𝒱ₖ → 𝒱ₖ by 𝒥ᵢ(m) = ∑_(a=1)^(2i−2) ω^(b)((a 2i−1) · m, m) (a 2i−1) · m, where m ∈ 𝒫ₖ and ω^(b) is the weight function of Definition 4.1. We interpret the formula for i = 1 as 𝒥₁ = 0 and refer to these operators collectively as 𝒥-operators.\" The displayed formula gives the coefficient at output p. The unique contributing input for each transposition is act(a,2i-2,p), because the transposition is its own inverse. Charges thus belong to p. The map is linear over K. J is extended by zero outside 1 ≤ i ≤ k. The bounds and indices use natural subtraction. Fin.mk(r) constructs the element of Fin(2k) with natural label r, with bounds supplied by 0 < i <= k and a : Fin(2i-2).", "J", true),
            Node("single", "Identity basis vector", SingleFormula(),
                "The identity basis vector has coefficient one at e(k) and zero at every other matching. Since P(k) is finite, all coefficient functions correspond to finite linear combinations of the paper's basis.", "single", true),
            Node("orbit", "Cyclic orbit of the generated algebra", OrbitFormula(),
                "Definition 5.3, page 34: \"For k a positive integer, let 𝒳(k) = ⟨𝒥₁, 𝒥₂, …, 𝒥ₖ⟩ · 𝔢ₖ ⊆ 𝒱ₖ. That is, 𝒳(k) is the orbit of 𝔢ₖ under the action of the algebra of 𝒥-operators.\" adjoin is the unital K-subalgebra generated by the range of i ↦ J(b,k,i). The extra generators are zero, so the range over all natural indices generates the same algebra as indices 1 through k. X is a set of coefficient functions, described by the displayed membership equivalence.", "X", true),
            Node("claim", "Coulter--Do Conjecture 5.4(a)", ClaimFormula(),
                "Conjecture 5.4(a), page 34: \"The 𝒥-operators commute when restricted to 𝒳(k) — that is, 𝒥ₘ 𝒥ₙ (v) = 𝒥ₙ 𝒥ₘ (v) for 1 ⩽ m ⩽ n ⩽ k and for all v ∈ 𝒳(k).\" The encoding quantifies over every positive natural k and all ordered indices in that interval. It uses K = RatFunc C, the rational-function field C(b), and b = RatFunc.X, an indeterminate. Operator equality on each v is equality of coefficient functions; b is never fixed to a complex number in the claim.", "claim", true),
            Node("result", "Refutation on X(6)", Disp(new Formula.Not(F.Id("claim"))),
                "Let v = J_6 J_6 J_5 J_4 J_3 e_6 and T = (1 5 | 2 7 | 3 9 | 4 11 | 6 10 | 8 12). The generating word places v in X(6). Coefficientwise ring-homomorphism transport embeds the integer-polynomial model into C(b), then evaluates its polynomial coefficients at 2. The T-coefficients of J_2 J_4 v and J_4 J_2 v evaluate to 78 and 81. Injectivity of the polynomial embedding shows that the original coefficients in C(b) cannot agree. A support invariant for increasing words and the forced partner at the top pair reduce the finite sums to a backward path.", "result", false, DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, bool literature, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("coulter-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula ExistsIn(Formula v, Formula type, Formula body) =>
        Seq(Exists, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ltq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Type => Named("Type");
    private static Formula PairType(Formula k) => Call("P", k);
    private static Formula LabelType(Formula k) => Call("Fin", Mul(D(2), k));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Partner(Formula p, Formula x) => Apply(Val(p), x);
    private static Formula VectorType(Formula k, Formula field) => Arrow(PairType(k), field);
    private static Formula Instance(string name, Formula field, Formula body) =>
        Seq(OpenBracket, Call(name, field), CloseBracket, Sp, body);
    private static Formula LambdaOf(Formula v, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Mod(Formula a) => Call("mod", a, D(2));
    private static Formula NatSub(Formula a, Formula b) => Call("natSub", a, b);

    private static Formula PairFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p"), x = F.Id("x");
        Formula conditions = And(All(x, LabelType(k), Eqn(Apply(p, Apply(p, x)), x)),
            All(x, LabelType(k), Ne(Apply(p, x), x)));
        Formula subtype = Seq(OpenBrace, p, Sp, Colon, Sp, Arrow(LabelType(k), LabelType(k)), Sp,
            Mid, Sp, conditions, CloseBrace);
        return Disp(All(k, Nat, Eqn(PairType(k), subtype)));
    }

    private static Formula IdentityFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x"), label = Val(x);
        Formula partner = Call("ite", Eqn(Mod(label), D(0)), Add(label, D(1)), NatSub(label, D(1)));
        return Disp(All(k, Nat, All(x, LabelType(k), Eqn(Val(Partner(Call("e", k), x)), partner))));
    }

    private static Formula ActionFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p"), a = F.Id("a"), c = F.Id("c"), x = F.Id("x");
        Formula swap = Call("swap", a, c);
        return Disp(All(k, Nat, All(a, LabelType(k), All(c, LabelType(k), All(p, PairType(k),
            All(x, LabelType(k), Eqn(Partner(Call("act", a, c, p), x),
                Apply(swap, Partner(p, Apply(swap, x))))))))));
    }

    private static Formula WalkFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p"), x = F.Id("x"), n = F.Id("n");
        Formula current = Call("walk", p, x, n);
        Formula step = Eqn(Call("walk", p, x, Add(n, D(1))),
            Call("ite", Eqn(Mod(n), D(0)), Partner(Call("e", k), current), Partner(p, current)));
        return Disp(All(k, Nat, All(p, PairType(k), All(x, LabelType(k),
            And(Eqn(Call("walk", p, x, D(0)), x), All(n, Nat, step))))));
    }

    private static Formula ChargeFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p"), x = F.Id("x"), s = F.Id("s"), n = F.Id("n");
        Formula u = Val(Call("walk", p, x, n));
        Formula update = LambdaOf(s, Seq(Nat, Times, Sp, Named("Bool")), LambdaOf(n, Nat,
            Call("ite", Ltq(Call("fst", s), u), Pair(u, Call("beq", Mod(n), D(0))), s)));
        Formula folded = Call("foldl", Parenthesized(update), Pair(Val(x), Named("true")), Call("range", Mul(D(2), k)));
        return Disp(All(k, Nat, All(p, PairType(k), All(x, LabelType(k),
            Eqn(Call("charge", p, x), Call("snd", folded))))));
    }

    private static Formula WeightFormula()
    {
        Formula field = F.Id("K"), b = F.Id("b"), k = F.Id("k"), p = F.Id("p"), a = F.Id("a"), c = F.Id("c");
        Formula weight = Eqn(Call("weight", b, p, a, c),
            Call("ite", Eqn(Call("charge", p, a), Call("charge", p, c)), D(1), b));
        return Disp(All(field, Type, Instance("One", field, All(b, field, All(k, Nat,
            All(p, PairType(k), All(a, LabelType(k), All(c, LabelType(k), weight))))))));
    }

    private static Formula OperatorFormula()
    {
        Formula field = F.Id("K"), b = F.Id("b"), k = F.Id("k"), i = F.Id("i"), w = F.Id("w"), p = F.Id("p"), a = F.Id("a");
        Formula bound = NatSub(Mul(D(2), i), D(2));
        Formula finMk = Seq(Operatorname, Grp(F.Id("Fin"), Dot, F.Id("mk"))); Formula aa = Apply(finMk, Val(a)), c = Apply(finMk, bound);
        Formula term = Mul(Call("weight", b, p, aa, c), Apply(w, Call("act", aa, c, p)));
        Formula sum = Seq(Sum, Underscore, Grp(a, Sp, Colon, Sp, Call("Fin", bound)), Sp, term);
        Formula valid = And(Ltq(D(0), i), Leq(i, k));
        Formula body = Eqn(Apply(Call("J", b, k, i), w, p), Call("ite", valid, sum, D(0)));
        return Disp(All(field, Type, Instance("CommRing", field, All(b, field, All(k, Nat, All(i, Nat,
            All(w, VectorType(k, field), All(p, PairType(k), body))))))));
    }

    private static Formula SingleFormula()
    {
        Formula field = F.Id("K"), k = F.Id("k"), p = F.Id("p");
        Formula body = Eqn(Parenthesized(Seq(Apply(Call("single", k), p), Sp, Colon, Sp, field)), Call("ite", Eqn(p, Call("e", k)), D(1), D(0)));
        return Disp(All(field, Type, Instance("Zero", field, Instance("One", field,
            All(k, Nat, All(p, PairType(k), body))))));
    }

    private static Formula OrbitFormula()
    {
        Formula field = F.Id("K"), b = F.Id("b"), k = F.Id("k"), v = F.Id("v"), a = F.Id("A"), i = F.Id("i");
        Formula generated = Call("adjoin", field, Call("range", LambdaOf(i, Nat, Call("J", b, k, i))));
        Formula membership = ExistsIn(a, Call("End", field, VectorType(k, field)),
            And(Member(a, generated), Eqn(Apply(a, Call("single", k)), v)));
        Formula body = Iffn(Member(v, Call("X", b, k)), membership);
        return Disp(All(field, Type, Instance("CommRing", field,
            All(b, field, All(k, Nat, All(v, VectorType(k, field), body))))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), n = F.Id("n"), v = F.Id("v");
        Formula field = Call("RatFunc", Complex), b = Seq(Operatorname, Grp(F.Id("RatFunc"), Dot, F.Id("X")));
        Formula left = Apply(Call("J", b, k, m), Apply(Call("J", b, k, n), v));
        Formula right = Apply(Call("J", b, k, n), Apply(Call("J", b, k, m), v));
        Formula body = All(k, Nat, Imp(Leq(D(1), k), All(m, Nat, All(n, Nat,
            Imp(Leq(D(1), m), Imp(Leq(m, n), Imp(Leq(n, k),
                All(v, VectorType(k, field), Imp(Member(v, Call("X", b, k)), Eqn(left, right))))))))));
        return Disp(Iffn(F.Id("claim"), body));
    }
}

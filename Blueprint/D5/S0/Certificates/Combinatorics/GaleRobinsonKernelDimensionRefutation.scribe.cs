using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics;

internal sealed class GaleRobinsonKernelDimensionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/beluhov2026diamond");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over the rational-function field Q(a,b,c), the proper Gale--Robinson type (1,3,6) has at least six independent elements in its parity-gauge invariant kernel. Beluhov's Conjecture 3 predicts five.",
        H("Beluhov's invariant-kernel dimension conjecture fails at type (1,3,6)"),
        Blocks(
            Node("parameters", "Independent parameter ring", Disp(Eqn(F.Id("Parameters"), Call("MvPolynomial", Call("Fin", D(3)), Rat))),
                "The three variables of Parameters are independent indeterminates over Q. This is the polynomial representation of the three Gale--Robinson coefficients, rather than a numerical assignment.", "Parameters", false),
            Node("field", "Coefficient field", Disp(Eqn(F.Id("K"), Call("FractionRing", F.Id("Parameters")))),
                "Section 2, page 5: \"let 𝒜Frac = ℤ(α) be the field of all integer-coefficient rational functions of α₁, α₂, …, α⌊n/2⌋.\" For the three-term Gale--Robinson recurrence, K is Q(a,b,c), the fraction field of Q[a,b,c], equivalently the field of integer-coefficient rational functions in these three variables.", "K", true),
            Node("a", "First coefficient", ParameterFormula("a", 0), "a is the image of the first polynomial variable under the canonical algebra map Parameters to K. X in this formula has variable type Fin(3) and coefficient ring Q.", "a", false),
            Node("b", "Second coefficient", ParameterFormula("b", 1), "b is the image of the second polynomial variable under the same algebra map.", "b", false),
            Node("c", "Third coefficient", ParameterFormula("c", 2), "c is the image of the third polynomial variable under the same algebra map.", "c", false),
            Node("type", "Gale--Robinson type", Disp(Eqn(F.Id("GRType"), Call("record", RatField("n1", Nat), RatField("n2", Nat), RatField("n3", Nat)))),
                "Section 10, page 23: \"Let 𝐧 = (n₁, n₂, n₃) with n₁, n₂, n₃ being positive integers such that n = n₁ + n₂ + n₃.\" GRType is a record with three natural-number fields n₁, n₂ and n₃. record lists the field names and their types; these names are labels, not free variables. Positivity is required by proper. n1(t), n2(t), n3(t) denote the corresponding projections.", "GRType", true),
            Node("order", "Order of a type", OrderFormula(), "The order is the sum of the three entries.", "order", true),
            Node("proper", "Proper types", ProperFormula(),
                "Section 10, page 24: \"We call a type 𝐧 proper if it is primitive and n₁, n₂, n₃ are pairwise distinct.\" Page 23 defines primitive by gcd(n₁,n₂,n₃) = 1. The formula includes the positive-entry condition from the definition of a type. gcd(n1(t),gcd(n2(t),n3(t))) is the joint gcd; all three distinctness conditions are present.", "proper", true),
            Node("exponents", "Finite exponent carrier", ExponentFormula(), "Exp(n) is the function type Fin(n) to Fin(n+1). val extracts a Fin element's natural-number label, or a subtype's underlying element, according to its argument. Every exponent in a degree-n monomial is at most n, so this finite carrier retains all relevant monomials.", "Exp", false),
            Node("admissible", "Parity-gauge constraints", AdmissibleFormula(),
                "Section 5, page 11: \"This is equivalent to each exponent tuple (d₀, d₁, …, dₙ₋₁) which occurs in Φ satisfying d₀e₀ + d₁e₁ + ⋯ + dₙ₋₁eₙ₋₁ = e₀ + e₁ + ⋯ + eₙ₋₁ for all integer e ∈ ℰ.\" Section 2, page 5 gives the even-order basis 1,i and the odd-order basis i,i mod 2,(i+1) mod 2. The formula states the degree and index-weight conditions and, for odd n, both parity-weight conditions. Section 10, page 24 says that ℰ depends only on the parity of n; this is the parity-only reading used here. mod is natural-number remainder; natSub is natural subtraction truncated at zero; natDiv is natural integer division, so natDiv(r,2) is floor(r/2), never rational division. ite(c,t,f) chooses t if c and f otherwise.", "admissible", true),
            Node("upsilon", "Gauge-homogeneous domain subspace", UpsilonFormula(),
                "Section 5, page 11: \"The polynomials Φ which satisfy our additional constraint form a linear subspace Υ⊠ of Υ.\" upsilon(n) is the K-span of the unit-coefficient monomials satisfying admissible. toFinsupp denotes the existing Mathlib equivalence Finsupp.equivFunOnFinite.symm from functions on Fin(n) to finitely supported functions. range is the image of its displayed function; monomial(e,r) has exponent e and coefficient r.", "upsilon", true),
            Node("variable", "Polynomial variables", VariableFormula(), "x(n,i) is X at label i when i<n, and zero otherwise, in MvPolynomial(Fin(n),K). finMk denotes Fin.mk and constructs a bounded index, with the branch inequality supplying its bound. This total extension leaves every variable of a proper type's recurrence inside its index range.", "x", false),
            Node("quadratic", "The Gale--Robinson recurrence form", QuadraticFormula(),
                "Section 10, page 23 gives sᵢsᵢ₊ₙ = a₁sᵢ₊ₙ₁sᵢ₊ₙ₂₊ₙ₃ + a₂sᵢ₊ₙ₂sᵢ₊ₙ₃₊ₙ₁ + a₃sᵢ₊ₙ₃sᵢ₊ₙ₁₊ₙ₂. C embeds an element of K as a constant polynomial. The three coefficients are encoded by a,b,c, and the complementary indices are sums of the other two type entries. In particular the last term for (1,3,6) is c X₆ X₄.", "quadratic", true),
            Node("substitution", "Homogenized shift substitution", SubstitutionFormula(), "substitution(t,i) replaces Xᵢ by X₀Xᵢ₊₁ for every nonterminal index and by quadratic(t) for the terminal index. The substitution keeps the source's zero-based variable labels.", "substitution", true),
            Node("phi", "The linear invariant operator", PhiFormula(),
                "Section 5, page 10 defines φ(Φ) = x₀^(n−2) R Φ − Φ(x₀x₁,x₀x₂,…,x₀xₙ₋₁,R), where R is the recurrence's quadratic form. phi is the K-linear map given by multiplication by x₀^(n−2)R minus evaluation at the homogenized substitution. aeval fixes coefficients in K. It is defined on the whole polynomial ring and then restricted through omega to upsilon(n); the source defines the operator on the homogeneous subspace.", "phi", true),
            Node("omega", "Restricted kernel", OmegaFormula(),
                "Section 5, page 11: \"Let Ω⊠ be the kernel of φ over Υ⊠.\" inf denotes submodule intersection. omega(t) is the intersection of upsilon(order(t)) and the kernel of phi(t), viewed as a K-submodule of the polynomial ring. Thus its elements satisfy both domain membership and the actual polynomial identity phi(t)(Φ)=0.", "omega", true),
            Node("claim", "Beluhov Conjecture 3", ClaimFormula(),
                "Conjecture 3, page 24: \"For every proper type 𝐧 of order n, it holds that dim Ω⊠ = ⌊n/2⌋.\" The encoding quantifies over all proper GRType records. Module.finrank is the dimension over K. It uses the source's stated parity-only gauge space and independent coefficients, without a finite-field specialization. Natural integer division order(t)/2 encodes the floor.", "claim", true),
            Node("result", "Refutation at type (1,3,6)", Disp(new Formula.Not(F.Id("claim"))),
                "The type (1,3,6) is proper and has order 10. Six explicit polynomials H₀,…,H₅ satisfy the degree-10, index-weight-45 constraints and phi(Hⱼ)=0. Their coefficients at exponent tuples 1111111111, 2011111021, 2101111012, 2110011211, 2110101121 and 2110110112 form diag(1,b,b²,c,bc²,bc). Because b and c are nonzero indeterminates in K, these six elements are independent. The domain subspace is spanned by a finite monomial set, so the restricted kernel is finite dimensional and its dimension is at least 6, contradicting the predicted 5. A matching upper bound is not asserted. The larger type-dependent gauge space obtained by imposing only the three nonzero recurrence terms is outside this statement.", "result", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("beluhov-2026-conjecture-3-dimension-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("beluhov-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula v, Formula type, Formula body) => Seq(Forall, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula LambdaOf(Formula v, Formula type, Formula body) => Seq(LambdaLower, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Ltq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula Order(Formula t) => Call("order", t);
    private static Formula Entry(int j, Formula t) => Call("n" + j, t);
    private static Formula PolynomialType(Formula n) => Call("MvPolynomial", Call("Fin", n), F.Id("K"));
    private static Formula Mod(Formula a) => Call("mod", a, D(2));
    private static Formula NatSub(Formula a, Formula b) => Call("natSub", a, b);
    private static Formula Half(Formula a) => Call("natDiv", a, D(2));
    private static Formula SumOver(Formula i, Formula type, Formula term) => Seq(Sum, Underscore, Grp(i, Sp, Colon, Sp, type), Sp, Parenthesized(term));
    private static Formula RatField(string name, Formula type) => Seq(Named(name), Sp, Colon, Sp, type);

    private static Formula ParameterFormula(string name, int i) => Disp(Eqn(F.Id(name),
        Apply(Call("algebraMap", F.Id("Parameters"), F.Id("K")), Call("X", D((byte)i)))));

    private static Formula OrderFormula()
    {
        Formula t = F.Id("t");
        return Disp(All(t, F.Id("GRType"), Eqn(Order(t), Add(Add(Entry(1,t), Entry(2,t)), Entry(3,t)))));
    }

    private static Formula ProperFormula()
    {
        Formula t = F.Id("t"), a = Entry(1,t), b = Entry(2,t), c = Entry(3,t);
        Formula conditions = And(Ltq(D(0),a), And(Ltq(D(0),b), And(Ltq(D(0),c),
            And(Eqn(Call("gcd",a,Call("gcd",b,c)),D(1)), And(Ne(a,b), And(Ne(a,c),Ne(b,c)))))));
        return Disp(All(t, F.Id("GRType"), Iffn(Call("proper",t), conditions)));
    }

    private static Formula ExponentFormula()
    {
        Formula n = F.Id("n");
        return Disp(All(n, Nat, Eqn(Call("Exp",n), Arrow(Call("Fin",n),Call("Fin",Add(n,D(1)))))));
    }

    private static Formula AdmissibleFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), i = F.Id("i"), finite = Call("Fin",n), di = Val(Apply(d,i));
        Formula degree = Eqn(SumOver(i,finite,di),n);
        Formula weight = Eqn(SumOver(i,finite,Mul(Val(i),di)),Half(Mul(n,NatSub(n,D(1)))));
        Formula evens = Eqn(SumOver(i,finite,Call("ite",Eqn(Mod(Val(i)),D(0)),di,D(0))),Half(Add(n,D(1))));
        Formula odds = Eqn(SumOver(i,finite,Call("ite",Eqn(Mod(Val(i)),D(1)),di,D(0))),Half(n));
        return Disp(All(n,Nat,All(d,Call("Exp",n),Iffn(Call("admissible",d),
            And(degree,And(weight,Imp(Eqn(Mod(n),D(1)),And(evens,odds))))))));
    }

    private static Formula UpsilonFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), r = F.Id("r"), i = F.Id("i");
        Formula subtype = Seq(OpenBrace,r,Sp,Colon,Sp,Call("Exp",n),Sp,Mid,Sp,Call("admissible",r),CloseBrace);
        Formula exponent = Apply(Seq(Operatorname,Grp(F.Id("Finsupp"),Dot,F.Id("equivFunOnFinite"),Dot,F.Id("symm"))),Parenthesized(LambdaOf(i,Call("Fin",n),Val(Apply(Val(d),i)))));
        Formula terms = Call("range",Parenthesized(LambdaOf(d,subtype,Call("monomial",exponent,D(1)))));
        return Disp(All(n,Nat,Eqn(Call("upsilon",n),Call("span",F.Id("K"),terms))));
    }

    private static Formula VariableFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        return Disp(All(n,Nat,All(i,Nat,Eqn(Call("x",n,i),
            Call("ite",Ltq(i,n),Call("X",Apply(Seq(Operatorname,Grp(F.Id("Fin"),Dot,F.Id("mk"))),i)),D(0))))));
    }

    private static Formula QuadraticFormula()
    {
        Formula t = F.Id("t"), n = Order(t);
        Formula Term(string coefficient, int j, int k, int l) => Mul(Mul(Call("C",F.Id(coefficient)),Call("x",n,Entry(j,t))),Call("x",n,Add(Entry(k,t),Entry(l,t))));
        return Disp(All(t,F.Id("GRType"),Eqn(Call("quadratic",t),Add(Add(Term("a",1,2,3),Term("b",2,3,1)),Term("c",3,1,2)))));
    }

    private static Formula SubstitutionFormula()
    {
        Formula t = F.Id("t"), i = F.Id("i"), n = Order(t), next = Add(Val(i),D(1));
        return Disp(All(t,F.Id("GRType"),All(i,Call("Fin",n),Eqn(Call("substitution",t,i),
            Call("ite",Ltq(next,n),Mul(Call("x",n,D(0)),Call("X",Apply(Seq(Operatorname,Grp(F.Id("Fin"),Dot,F.Id("mk"))),next))),Call("quadratic",t))))));
    }

    private static Formula PhiFormula()
    {
        Formula t = F.Id("t"), p = F.Id("P"), n = Order(t);
        Formula left = Mul(Mul(Pow(Call("x",n,D(0)),NatSub(n,D(2))),Call("quadratic",t)),p);
        Formula right = Apply(Call("aeval",Call("substitution",t)),p);
        return Disp(All(t,F.Id("GRType"),All(p,PolynomialType(n),Eqn(Apply(Call("phi",t),p),Sub(left,right)))));
    }

    private static Formula OmegaFormula()
    {
        Formula t = F.Id("t");
        return Disp(All(t,F.Id("GRType"),Eqn(Call("omega",t),Call("inf",Call("upsilon",Order(t)),Call("ker",Call("phi",t))))));
    }

    private static Formula ClaimFormula()
    {
        Formula t = F.Id("t");
        return Disp(Iffn(F.Id("claim"),All(t,F.Id("GRType"),Imp(Call("proper",t),
            Eqn(Call("finrank",F.Id("K"),Call("omega",t)),Half(Order(t)))))));
    }
}

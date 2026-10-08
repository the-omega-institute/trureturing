using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class StampachWaclawekExpansionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/stampachwaclawek2026birman");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Birman weight expansion conjecture fails at order two and p = 11/10.",
        H("Štampach–Waclawek Expansion Refutation"),
        Blocks(
            Entry("parameter-sequence", "gT", "The alternative parameter sequence", GT(),
                "Equation (2.16), p. 9, defines gT by n^(1−1/p) times the product "
                + "of n−j for j=1,…,ℓ−1 on non-negative integers, with zero extension "
                + "on negative integers. The product is over Finset.Icc on natural indices; "
                + "ℓ−1 there is natural subtraction. All explicitly displayed casts to ℝ "
                + "are the Lean coercions. Real powers use Real.rpow.", DescribeRole.Definition, true),
            Entry("gradient", "grad", "The discrete gradient", Difference(false),
                "Equation (2.2), p. 3: “We introduce the discrete gradient and discrete "
                + "divergence operators acting on C(ℤ) as” (∇u)ₙ := uₙ − uₙ₋₁ and "
                + "(div u)ₙ := uₙ₊₁ − uₙ. Here the sequences take real values, "
                + "a subdomain of the source's complex sequences.", DescribeRole.Definition, true),
            Entry("divergence", "dv", "The discrete divergence", Difference(true),
                "Equation (2.2), p. 3, defines the forward difference u(n+1)−u(n). "
                + "The indices are integers, so the successor does not truncate.", DescribeRole.Definition, true),
            Entry("signed-power", "spow", "The signed-power convention", SignedPower(),
                "After (2.3), p. 4: “where ν^{⟨a⟩}:=ν|ν|^{a−1} for any a>0 and ν∈ℂ, "
                + "with the convention 0^{⟨a⟩}:=0.” The real restriction is represented by spow; "
                + "its definition includes the zero branch for every real exponent.", DescribeRole.Definition, true),
            Entry("weight", "rhoT", "The alternative weight", Weight(),
                "Equation (2.17), p. 9, divides −Δₚ^(ℓ)gT by gT^(p−1). "
                + "Equation (2.3), p. 4, gives −Δₚ^(ℓ)u = (−1)^ℓ div^ℓ(∇^ℓu)^{⟨p−1⟩}. "
                + "The bracketed exponent [ℓ] means Function.iterate, including zero iterations; "
                + "it is not a scalar power. The displayed expression retains the sign factor, "
                + "order of the iterates, signed power and denominator.", DescribeRole.Definition, true),
            Entry("expansion-claim", "claim", "The non-negative expansion claim", Claim(),
                "Conjecture 5.6(iii), p. 28, states verbatim: “For all n ≥ ℓ, the terms "
                + "ρ̃ₙ^(ℓ,p) admit a power series expansion in negative powers of n with entirely "
                + "non-negative coefficients; cf. (2.15).” The preceding sentence is: "
                + "“Let ℓ ∈ ℕ and p > 1, and let ρ̃^(ℓ,p) be defined by (2.17) and (2.16).” "
                + "The source's ℕ denotes positive integers; Lean uses ℓ : ℕ with 1 ≤ ℓ. "
                + "HasSum expresses convergence of one coefficient sequence at every n ≥ ℓ. "
                + "This claim allows any non-negative constant coefficient. It follows from "
                + "the source's (2.15) form by c₀=((1/q) rising-factorial ℓ)^p and cₖ=c₀Aₖ for k≥1, "
                + "where (1/q)ℓ is the positive rising factorial. Hence negating this weaker "
                + "claim refutes (iii) as stated.", DescribeRole.Definition, true),
            Entry("refutation", "result", "The expansion conjecture is false", Disp(Seq(Neg, Sp, F.Id("claim"))),
                "Take ℓ=2 and p=11/10. Rational enclosures of n^(2p)rhoT(2,p,n) "
                + "at n=100,200,400 give 200G(100)−600G(200)+400G(400) ≤ −32183/312500000 < 0. "
                + "Here G(n) denotes that normalized weight. This is the difference between the upper and lower "
                + "adjacent secant slopes at x=1/n. Non-negative power-series coefficients "
                + "force the opposite inequality. The proof excludes an expansion directly; "
                + "it does not identify individual asymptotic coefficients. Only part (iii) "
                + "is refuted. Parts (i) and (ii), and the source's original-weight conjecture "
                + "in Remark 2.12, are separate questions.", DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Commentary(name, prose), role);
    private static BlockSequence Commentary(string name, string prose)
    {
        if (name != "claim") return Blocks(Paragraph(Text(prose)));
        Formula p = F.Id("p"), n = F.Id("n");
        Formula rho = new Formula.Power(Seq(Widetilde, Grp(Rho)),
            Parenthesized(Seq(Ell, Comma, p)));
        return Blocks(
            Paragraph(Text("Conjecture 5.6, p. 28: “Let "),
                Math(Seq(Ell, Sp, InMacro, Sp, Nat)), Text(" and "),
                Math(Seq(p, Gt, Sp, D(1))), Text(", and let "), Math(rho),
                Text(" be defined by (2.17) and (2.16).”")),
            Paragraph(Text("Part (iii), verbatim: “For all "), Math(Seq(n, Ge, Sp, Ell)),
                Text(", the terms "), Math(new Formula.Subscript(rho, n)),
                Text(" admit a power series expansion in negative powers of "), Math(n),
                Text(" with entirely non-negative coefficients; cf. (2.15).”")),
            Paragraph(Text("The source's ℕ denotes positive integers; Lean uses ℓ : ℕ "
                + "with 1 ≤ ℓ. HasSum expresses convergence of one coefficient sequence "
                + "at every n ≥ ℓ. The constant coefficient is allowed to be any "
                + "non-negative number. The source's (2.15) form implies this claim: "
                + "take c₀=((1/q) rising-factorial ℓ)^p and cₖ=c₀Aₖ for k≥1. "
                + "The rising factorial is positive for ℓ≥1 and p>1. Negating this "
                + "weaker claim therefore refutes (iii) as stated.")));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Q(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula CastReal(Formula x) => Parenthesized(Seq(x, Colon, Sp, Real));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Iterate(string name, Formula ell, Formula u, Formula n) =>
        At(Seq(Operatorname, Grp(F.Id(name)), Caret, Grp(OpenBracket, ell, CloseBracket)), u, n);
    private static Formula Cases(Formula first, Formula condition, Formula second) =>
        Seq(Begin, Grp(F.Id("cases")), first, Amp, F.Text, Grp(F.Id("if")), Sp,
            condition, RowBreak, second, Amp, F.Text, Grp(F.Id("otherwise")), End, Grp(F.Id("cases")));

    private static Formula GT()
    {
        Formula ell = Ell, p = F.Id("p"), n = F.Id("n"), j = F.Id("j");
        Formula icc = At(Seq(Operatorname, Grp(F.Id("Finset")), Dot,
            Operatorname, Grp(F.Id("Icc"))), D(1), Sub(ell, D(1)));
        Formula product = Seq(Prod, Underscore, Grp(j, InMacro, Sp, icc), Sp,
            Parenthesized(Sub(CastReal(n), CastReal(j))));
        Formula rhs = Cases(Mul(Pow(CastReal(n), Sub(D(1), Q(D(1), p))), product),
            Leq(D(0), n), D(0));
        return Disp(All(ell, Nat, All(p, Real, All(n, Ints, Eqn(Call("gT", ell, p, n), rhs)))));
    }

    private static Formula Difference(bool forward)
    {
        Formula u = F.Id("u"), n = F.Id("n");
        Formula rhs = forward ? Sub(At(u, Add(n, D(1))), At(u, n))
            : Sub(At(u, n), At(u, Sub(n, D(1))));
        return Disp(All(u, Seq(Ints, To, Sp, Real), All(n, Ints,
            Eqn(Call(forward ? "dv" : "grad", u, n), rhs))));
    }

    private static Formula SignedPower()
    {
        Formula a = F.Id("a"), nu = Nu;
        Formula rhs = Cases(D(0), Eqn(nu, D(0)), Mul(nu, Pow(new Formula.Absolute(nu), Sub(a, D(1)))));
        return Disp(All(a, Real, All(nu, Real, Eqn(Call("spow", a, nu), rhs))));
    }

    private static Formula Weight()
    {
        Formula ell = Ell, p = F.Id("p"), n = F.Id("n"), m = F.Id("m");
        Formula signed = Lambda(m, Ints,
            Call("spow", Sub(p, D(1)), Iterate("grad", ell, Call("gT", ell, p), m)));
        Formula numerator = Mul(Pow(Parenthesized(Seq(Minus, D(1))), ell), Iterate("dv", ell, signed, n));
        Formula rhs = Q(numerator, Pow(Call("gT", ell, p, n), Sub(p, D(1))));
        return Disp(All(ell, Nat, All(p, Real, All(n, Ints, Eqn(Call("rhoT", ell, p, n), rhs)))));
    }

    private static Formula Claim()
    {
        Formula ell = Ell, p = F.Id("p"), c = F.Id("c"), k = F.Id("k"), n = F.Id("n");
        Formula coefficientCondition = All(k, Nat, Leq(D(0), At(c, k)));
        Formula series = Lambda(k, Nat, Q(At(c, k), Pow(CastReal(n), k)));
        Formula value = Mul(Pow(CastReal(n), Mul(CastReal(ell), p)),
            Call("rhoT", ell, p, Parenthesized(Seq(n, Colon, Sp, Ints))));
        Formula sums = All(n, Nat, Imp(Leq(ell, n), Call("HasSum", series, value)));
        Formula expansion = Ex(c, Seq(Nat, To, Sp, Real), And(coefficientCondition, sums));
        Formula body = All(ell, Nat, Imp(Leq(D(1), ell),
            All(p, Real, Imp(Less(D(1), p), expansion))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}

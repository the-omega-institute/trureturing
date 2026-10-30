using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HypergeometricShiftTuran;

internal sealed class FunctionResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2017pfq");
    private const string Prefix = "D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A convergent-series counterexample to the function clause of Conjecture 1.",
        H("The function Turanian can be negative"), Blocks(
            Describe.Lean(DescribeId.Create("gamma-series-function"),
                DeclarationHandle.Create(Prefix + "fval"),
                H("The function in equation (10)"), StatementSource.FromAuthor(Disp(FunctionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (10), page 5 of arXiv:1611.06724v1: “f (µ; x) = Γ(a + µ)/Γ(b + µ) pFq(a + µ; b + µ; x) = ∑ₙ₌₀∞ Γ(a + µ + n)/Γ(b + µ + n) xⁿ/n!.” Vector Gamma values denote products over entries. The Lean definition is the real tsum of Defs.coeff a b (mu+n) times x to the power n divided by n factorial. At the counterexample all three series converge, as follows from the Gamma recurrence and a geometric bound after index eight."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gamma-series-function-turanian"),
                DeclarationHandle.Create(Prefix + "turanian"),
                H("The function Turanian"), StatementSource.FromAuthor(Disp(TuranianFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (9), page 5: “∆f (α, β; x) := f (µ + α; x)f (µ + β; x) − f (µ; x)f (µ + α + β; x) = ∑ₘ₌₀∞ δm xᵐ”. The definition retains the two shifted products with exactly this subtraction order."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture-one-function-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The universal function assertion"), StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 3, page 5: “Theorem 3. If p ≤ q and conditions (13) are satisfied, then ∆f (α, β; x) ≥ 0 for x ≥ 0, µ, β ≥ 0 and α ∈ N, where ∆f (α, β; x) is defined in (9) with f from (10). Moreover, if α ≤ β + 1, then δm ≥ 0 for all m ∈ N0.”")),
                    Paragraph(Text("Conjecture 1, page 6: “Conjecture 1. All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.” The claim is its function clause in the branch 1 ≤ p ≤ q: all positive numerator and denominator parameter vectors satisfying Defs.cond13, all mu at least one, all nonnegative alpha, beta and x. It imposes no alpha at most beta+1 condition, since that restriction belongs to the coefficient clause. Section 2, page 3, states: “We will always assume that a₂ is not empty (i.e. p₂ ≥ 1), while all other subvectors are allowed to be empty.” It continues: “In this section we will consider log-convexity of the function f (µ; x) defined in (3) under these assumptions.” Section 3 sets a₁ and b₁ empty, so a=a₂. Whether nonemptiness carries into that section or is local to Section 2, the witness with p=1 belongs to the domain. Refuting the claim with 1 ≤ p refutes both readings."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture-one-function-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Refutation by an exact series estimate"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take p=1, a=(1), q=12, every denominator parameter equal to one half, mu=1, alpha=beta=1/2 and x=2000. Write fval at mu=3/2 as sqrt(pi) times A′, fval at mu=1 as pi to the power -6 times R, and fval at mu=2 as pi to the power -6 times S. The integer and half-integer Gamma formulas give positive rational series for A′, R and S.")),
                    Paragraph(Text("Use the first ten terms for each series. The tail of A′ is at most its term of index ten divided by 1-rho, where rho=74/100000000000 bounds every successive ratio after index nine. The resulting upper bound for A′ is at most 1672/1000. The first ten rational terms of R sum to at least 136700 and those of S to at least 69; these lower bounds already follow from their first three terms. Mathlib's pi<3.1416 and exact rational arithmetic give (1672/1000) squared times pi to the power 13 less than 136700 times 69. Hence pi times A′ squared is strictly smaller than pi to the power -12 times R times S. The Turanian is strictly negative.")),
                    Paragraph(Text("The numerator is nonempty and all parameters are positive. Condition (13) reduces to (1/2)^12 ≤ 12(1/2)^11; the dimensions and nonnegative shifts satisfy every hypothesis of claim. Thus universal function nonnegativity is false. Theorem 3's integer-shift statement is unaffected by these two half shifts."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kalmykov-karp-pfq-conjecture-one-function"),
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
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Parameters(Formula body) =>
        All("p", N, All("q", N,
            All("a", new Formula.TypeArrow(Call("Fin", V("p")), R),
            All("b", new Formula.TypeArrow(Call("Fin", V("q")), R), body))));
    private static Formula Scalars(Formula body) =>
        All("mu", R, All("alpha", R, All("beta", R, All("x", R, body))));
    private static Formula Value(Formula shift) => Call("fval", V("a"), V("b"), shift, V("x"));
    private static Formula FunctionFormula()
    {
        var n = V("n");
        var summand = Mul(Call("Defs.coeff", V("a"), V("b"), Add(V("mu"), n)),
            new Formula.Fraction(new Formula.Power(V("x"), n), Call("Nat.factorial", n)));
        return Parameters(All("mu", R, All("x", R,
            Eqn(Value(V("mu")), Seq(new Formula.Subscript(Seq(Sum, Apos),
                Seq(n, Colon, Sp, N)), Sp, summand)))));
    }
    private static Formula TuranianFormula() => Parameters(Scalars(
        Eqn(Call("turanian", V("a"), V("b"), V("mu"), V("alpha"), V("beta"), V("x")),
            new Formula.Binary(Mul(Value(Add(V("mu"), V("alpha"))), Value(Add(V("mu"), V("beta")))),
                FormulaBinaryOperator.Subtract,
                Mul(Value(V("mu")), Value(Add(Add(V("mu"), V("alpha")), V("beta"))))))));
    private static Formula ClaimFormula() => Eqn(V("claim"), ClaimBody());
    private static Formula ClaimBody()
    {
        var body = Leq(D(0), Call("turanian", V("a"), V("b"), V("mu"), V("alpha"), V("beta"), V("x")));
        var scalars = Scalars(Imp(Leq(D(1), V("mu")), Imp(Leq(D(0), V("alpha")),
            Imp(Leq(D(0), V("beta")), Imp(Leq(D(0), V("x")), body)))));
        var chain = Imp(Call("Defs.cond13", V("a"), V("b")), scalars);
        var positiveB = Imp(All("j", Call("Fin", V("q")), Positive(new Formula.Apply(V("b"), [V("j")]))), chain);
        var positiveA = Imp(All("i", Call("Fin", V("p")), Positive(new Formula.Apply(V("a"), [V("i")]))), positiveB);
        return Parameters(Imp(Leq(D(1), V("p")), Imp(Leq(V("p"), V("q")), positiveA)));
    }
}

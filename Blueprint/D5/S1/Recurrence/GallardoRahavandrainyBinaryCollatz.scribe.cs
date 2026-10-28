using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GallardoRahavandrainyBinaryCollatzDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/gallardo2023binarycollatz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary-polynomial Collatz length of (M²+M+1)ⁿ equals n+1 for n≥2.",
        H("Gallardo–Rahavandrainy's Binary-Polynomial Collatz Conjecture"),
        Blocks(
            Paragraph(Text("All polynomials have coefficients in ZMod 2. Polynomial.X is the "
                + "indeterminate, and the natural index k corresponds to the source index 2k+1. "
                + "The operation divByMonic is polynomial division by a monic polynomial; "
                + "rootMultiplicity records the multiplicity of a specified root. In characteristic "
                + "two, X-C(1)=X+1. The least hitting index is taken with sInf on natural numbers; "
                + "the proof establishes a hit for every polynomial used in the conclusion.")),
            Node("M", "The first nonconstant odd polynomial", Disp(Equal(
                Typed(F.Id("M"), Polynomials()), Add(Add(Pow(X(), D(2)), X()), D(1)))),
                "\"The first odd polynomial after 1 is M := x² + x + 1.\" (p. 2.) "
                + "The source also says that A is odd if gcd(A, x(x + 1)) = 1. "
                + "This is Mathlib's IsCoprime A (X*(X+1)).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("oddPart", "Removing the linear factors", OddPartFormula(),
                "\"S = x^{val_x(S)}(x + 1)^{val_{x+1}(S)} S₁, where S₁ is odd.\" (p. 2.) "
                + "The two valuations are rootMultiplicity at 0 and 1. The quotient by their "
                + "product is S₁ for a nonzero S; the Lean definition is total at S=0 as well.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("oddSeq", "The odd Collatz sequence", OddSeqFormula(),
                "\"A₁ the odd polynomial such that A₀ = x^{a₀}(x + 1)^{b₀}A₁\" and "
                + "\"A_{2k} = 1 + MA_{2k−1}\", "
                + "\"A_{2k+1} = A_{2k}/(x^{a_{2k}}(x + 1)^{b_{2k}}).\" (p. 2.) "
                + "Thus oddSeq A 0 is A₁, and oddSeq A k is A_{2k+1}.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("collatzLength", "Counting the odd terms", LengthFormula(),
                "Theorem 1.2 gives \"[A₀, …, A_{2m−2}, x² + x] and [A₁, …, A_{2m−1}, 1]\" "
                + "and \"where m ∈ ℕ*, ℓ_A = m + 1 ≤ 2^{deg(A)−1}.\" (p. 3.) "
                + "The length includes the initial odd term and the terminal 1. For n=9, "
                + "the source's table has ten odd terms and length 10 (p. 15).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 3.11", Disp(Equivalent(F.Id("claim"), ClaimBody())),
                "\"If A = (M² + M + 1)ⁿ with n ≥ 2, then ℓ_A equals n + 1.\" "
                + "(Conjecture 3.11, p. 15.) The exponent n is a natural number and "
                + "collatzLength is the number of terms just defined.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("nonzero_of_odd", "Evaluation one implies nonzero", NonzeroFromEvalFormula(),
                "A polynomial whose value at zero is one is nonzero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("nonzero_eq_one", "The unique nonzero binary coefficient", BinaryCoefficientFormula(),
                "Every nonzero element of ZMod 2 equals one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("eq_one_of_degree_zero", "An odd constant polynomial", ConstantOneFormula(),
                "A polynomial of natural degree zero whose value at zero is one equals one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("degree_q", "Degree of the multiplier", Disp(Equal(
                App(Q("Polynomial", "natDegree"), F.Id("M")), D(2))),
                "The multiplier M has natural degree two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("q_ne_zero", "The multiplier is nonzero", Disp(NotEqual(F.Id("M"), D(0))),
                "The multiplier M is nonzero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("oddPart_factor", "The odd part of a factored polynomial", OddPartFactorFormula(),
                "If u takes value one at both zero and one, removing powers of X and X-C(1) "
                + "from their product with u leaves exactly u.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Proof of Conjecture 3.11", Disp(ClaimBody()),
                "Substitution of x(x+1) and polynomial reversal identify the odd sequence "
                + "with the map f ↦ (1+X)f+X^(natDegree f+1). A degree-gap reduction proves "
                + "termination and relates its first hitting times. For every f with f(0)=1, "
                + "squaring doubles the hitting time, and multiplying its square by 1+X+X² "
                + "adds one to twice that time. Strong induction on n, using its even and odd "
                + "cases, gives hitting time n for (1+X+X²)ⁿ. Transport to the source sequence "
                + "therefore gives length n+1. The same proof gives this length also for n=0 "
                + "and n=1. No sharper general upper bound for other initial polynomials is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gallardo-rahavandrainy-2023-binary-collatz-3-11"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("grcollatz-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Polynomials() => Call("Polynomial", Call("ZMod", D(2)));
    private static Formula X() => Q("Polynomial", "X");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Equivalent(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Iff, Sp, Parenthesized(right));

    private static Formula OddPartFormula()
    {
        var s = F.Id("S");
        var multiplicity = Seq(s, Dot, Operatorname, Grp(F.Id("rootMultiplicity")));
        var denominator = Multiply(Pow(X(), App(multiplicity, D(0))),
            Pow(Subtract(X(), App(Q("Polynomial", "C"), D(1))), App(multiplicity, D(1))));
        return Disp(All("S", Polynomials(), Equal(Call("oddPart", s),
            App(Q("Polynomial", "divByMonic"), s, denominator))));
    }

    private static Formula OddSeqFormula()
    {
        var a = F.Id("A");
        var k = F.Id("k");
        var first = Equal(Call("oddSeq", a, D(0)), Call("oddPart", a));
        var next = All("k", Naturals(), Equal(Call("oddSeq", a, Add(k, D(1))),
            Call("oddPart", Add(D(1), Multiply(F.Id("M"), Call("oddSeq", a, k))))));
        return Disp(All("A", Polynomials(), Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(next))));
    }

    private static Formula LengthFormula()
    {
        var a = F.Id("A");
        var k = F.Id("k");
        var hits = Seq(OpenBrace, Typed(k, Naturals()), Sp, Bar, Sp,
            Equal(Call("oddSeq", a, k), D(1)), CloseBrace);
        return Disp(All("A", Polynomials(), Equal(Call("collatzLength", a),
            Add(Call("sInf", hits), D(1)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var polynomial = Add(Add(Pow(F.Id("M"), D(2)), F.Id("M")), D(1));
        var lower = new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = Equal(Call("collatzLength", Pow(polynomial, n)), Add(n, D(1)));
        return All("n", Naturals(), Seq(Parenthesized(lower), Sp, Implies, Sp, Parenthesized(conclusion)));
    }
    private static Formula Implication(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula At(Formula f, Formula x) => App(Q("Polynomial", "eval"), x, f);

    private static Formula NonzeroFromEvalFormula()
    {
        var f = F.Id("f");
        return Disp(All("f", Polynomials(), Implication(Equal(At(f, D(0)), D(1)), NotEqual(f, D(0)))));
    }

    private static Formula BinaryCoefficientFormula()
    {
        var c = F.Id("c");
        return Disp(All("c", Call("ZMod", D(2)), Implication(NotEqual(c, D(0)), Equal(c, D(1)))));
    }

    private static Formula ConstantOneFormula()
    {
        var f = F.Id("f");
        return Disp(All("f", Polynomials(), Implication(Equal(At(f, D(0)), D(1)),
            Implication(Equal(App(Q("Polynomial", "natDegree"), f), D(0)), Equal(f, D(1))))));
    }

    private static Formula OddPartFactorFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var u = F.Id("u");
        var factored = Multiply(Multiply(Pow(X(), a), Pow(Subtract(X(), App(Q("Polynomial", "C"), D(1))), b)), u);
        return Disp(All("a", Naturals(), All("b", Naturals(), All("u", Polynomials(),
            Implication(Equal(At(u, D(0)), D(1)), Implication(Equal(At(u, D(1)), D(1)),
                Equal(Call("oddPart", factored), u)))))));
    }

}

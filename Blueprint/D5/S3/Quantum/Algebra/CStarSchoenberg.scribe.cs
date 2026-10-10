using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CStarSchoenbergDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CStarSchoenberg.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/krishna2022cstarschoenberg");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cubic polynomial over two by two complex matrices refutes Krishna’s C*-algebraic conjecture.",
        H("CStarSchoenberg"), Blocks(
            Node("orderedDeriv", "The ordered derivative", OrderedFormula(),
                "Section 2, p. 2: “Let 𝒜 be a C*-algebra. Given P(z) ≔ (z−a₁)(z−a₂)⋯(z−a_d) for all z∈𝒜 with a₁, a₂, …, a_d ∈ 𝒜, we define P′(z)=∑_{j=1}^d (z−a₁)⋯(z−aⱼ)̂⋯(z−a_d), ∀z∈𝒜 where the term with cap is missing.” List.eraseIdx removes the j-th factor, preserving the order of the other factors. Its index is the natural number val(j).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("DerivFactors", "Factorization on the entire algebra", FactorsFormula(),
                "Conjecture 2.1, p. 2: “If P′ can be written as P′(z)=d(z−b₁)(z−b₂)⋯(z−b_{d−1}) on 𝒜 with b₁, b₂, …, b_{d−1} ∈ 𝒜”. The equality is required for every z in A. The scalar d acts by natural repeated addition.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("y", "The second matrix in the example", Eq(Seq(F.Id("y"), Colon, Matrix2()), Add(Unit(0, 0), Unit(0, 1))),
                "The matrix units use zero-based indices. Thus y has first row (1,1) and second row (0,0).", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("a", "The three polynomial factors", AFormula(),
                "The three entries sum to zero. The matrix Matrix.single 0 1 1 is the off-diagonal matrix unit.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("u", "A critical point", Eq(Seq(F.Id("u"), Colon, Matrix2()), Smul(new Formula.Fraction(D(1), Cast(D(3))), Add(Unit(0, 1), F.Id("y")))),
                "This matrix and its negative are the two ordered derivative factors.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("b", "The two derivative factors", BFormula(),
                "The Fin 2 tuple is (u,−u).", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sum_a", "The factor sum vanishes", Eq(Sum("j", D(3), At("a", "j")), D(0)),
                "The entries of the three matrices cancel.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("factorization", "The ordered derivative factors for every matrix", Call("DerivFactors", D(3), F.Id("a"), F.Id("b")),
                "Entrywise multiplication for an arbitrary complex two by two matrix gives the factorization, without assuming the variable commutes with the factors.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("negative_e11_not_posSemidef", "A negative diagonal entry excludes positivity", All("c", Real(), Imp(new Formula.Relation(F.Id("c"), FormulaRelationOperator.LessThan, D(0)), new Formula.Not(Call("Matrix.PosSemidef", Smul(Seq(Parenthesized(Seq(F.Id("c"), Colon, Complex()))), Unit(0, 0)))))),
                "A positive-semidefinite matrix has nonnegative diagonal entries. The first diagonal entry is the real number c.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("claimSchoenberg", "Krishna\u2019s Conjecture 2.1", new Formula.Logic(F.Id("claimSchoenberg"), FormulaLogicOperator.Iff, ClaimBody(1)),
                "Conjecture 2.1 (C*-algebraic Schoenberg Conjecture), pp. 2–3: “Let 𝒜 be a C*-algebra. Let d∈ℕ\\{1}, P(z) ≔ (z−a₁)(z−a₂)⋯(z−a_d) be a polynomial over 𝒜 with a₁, a₂, …, a_d ∈ 𝒜. If P′ can be written as P′(z)=d(z−b₁)(z−b₂)⋯(z−b_{d−1}) on 𝒜 with b₁, b₂, …, b_{d−1} ∈ 𝒜, then” the two inequalities displayed below. The encoding uses zero-based Fin d and Fin (d−1), complex scalar multiplication, star and the C*-order. It restricts the source to d≥2 and unital C*-algebras in Type with PartialOrder and StarOrderedRing; this weakens the assertion, so its negation refutes the source statement.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture is false", new Formula.Not(F.Id("claimSchoenberg")),
                "At degree three the matrices a and b satisfy the factorization hypothesis. The first inequality has right side minus left side equal to −2/9 times Matrix.single 0 0 1. Its first diagonal entry is negative, contradicting the C*-order.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("krishna-2022-cstar-schoenberg"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Named(string name) => name switch
    {
        "Matrix.single" => Qualified("Matrix", "single"),
        "Matrix.PosSemidef" => Qualified("Matrix", "PosSemidef"),
        "List.ofFn" => Qualified("List", "ofFn"),
        "List.prod" => Qualified("List", "prod"),
        "List.eraseIdx" => Qualified("List", "eraseIdx"),
        _ => Seq(Operatorname, Grp(F.Id(name)))
    };
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(Parenthesized(l), FormulaLogicOperator.Implies, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(Parenthesized(l), FormulaLogicOperator.And, Parenthesized(r));
    private static Formula All(string v, Formula type, Formula body) => Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, byte n) => new Formula.Power(Parenthesized(a), D(n));
    private static Formula Star(Formula a) => Call("star", a);
    private static Formula Smul(Formula c, Formula a) => Seq(Parenthesized(c), Sp, Cdot, Sp, Parenthesized(a));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Matrix2() => Call("Matrix", Fin(D(2)), Fin(D(2)), Complex());
    private static Formula Unit(byte i, byte j) => Parenthesized(Seq(Call("Matrix.single", D(i), D(j), Parenthesized(Seq(D(1), Colon, Complex()))), Colon, Matrix2()));
    private static Formula At(string a, string j) => new Formula.Apply(F.Id(a), [F.Id(j)]);
    private static Formula Sum(string j, Formula n, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(F.Id(j), Colon, Fin(n))), Parenthesized(body));
    private static Formula Cast(Formula d) => Parenthesized(Seq(d, Colon, Complex()));
    private static Formula Coeff(byte n, byte p) => new Formula.Fraction(D(n), new Formula.Power(Cast(F.Id("d")), D(p)));
    private static Formula ShiftCoeff(byte n) => new Formula.Fraction(Sub(Cast(F.Id("d")), D(n)), Cast(F.Id("d")));
    private static Formula Energy(string a, bool reverse, bool square, Formula n)
    {
        var v = At(a, a == "a" ? "j" : "k");
        var product = reverse ? Mul(Star(v), v) : Mul(v, Star(v));
        return Sum(a == "a" ? "j" : "k", n, square ? Pow(product, 2) : product);
    }
    private static Formula ClaimBody(int which)
    {
        Formula d = F.Id("d"), A = F.Id("A");
        Formula z = F.Id("z");
        Formula aList = Call("List.ofFn", Seq(Parenthesized(Seq(F.Id("i"), Colon, Fin(d))), Sp, Mapsto, Sp, Sub(z, At("a", "i"))));
        Formula bList = Call("List.ofFn", Seq(Parenthesized(Seq(F.Id("k"), Colon, Fin(Sub(d, D(1))))), Sp, Mapsto, Sp, Sub(z, At("b", "k"))));
        Formula factorHypothesis = All("z", A, Eq(Sum("j", d, Call("List.prod", Call("List.eraseIdx", aList, Call("val", F.Id("j"))))), Smul(d, Call("List.prod", bList))));
        Formula S = Sum("j", d, At("a", "j"));
        Formula Pair(bool rev)
        {
            Formula en = Energy("a", rev, false, d), rhs;
            if (which == 1)
                rhs = Add(Smul(Coeff(1, 2), rev ? Mul(Star(S), S) : Mul(S, Star(S))), Smul(ShiftCoeff(2), en));
            else if (which == 2)
                rhs = Add(Smul(Coeff(2, 2), Pow(en, 2)), Smul(ShiftCoeff(4), Energy("a", rev, true, d)));
            else
            {
                Formula s = F.Id("S"), t = F.Id("T"), aj = At("a", "j");
                Formula shifted = Add(aj, Smul(Coeff(1, 1), s));
                Formula fourth = rev ? Mul(Mul(Mul(Star(aj), Star(shifted)), shifted), aj) : Mul(Mul(Mul(aj, shifted), Star(shifted)), Star(aj));
                Formula last = rev ? Mul(Mul(Mul(Star(aj), Star(s)), s), aj) : Mul(Mul(Mul(aj, s), Star(s)), Star(aj));
                rhs = Sub(Add(Add(Add(Smul(ShiftCoeff(6), Energy("a", rev, true, d)), Smul(Coeff(1, 2), Pow(en, 2))),
                    Smul(Coeff(1, 2), rev ? Mul(Star(t), t) : Mul(t, Star(t)))), Smul(Coeff(2, 1), Sum("j", d, fourth))),
                    Smul(Coeff(4, 3), Sum("j", d, last)));
            }
            return Le(Energy("b", rev, which != 1, Sub(d, D(1))), rhs);
        }
        Formula inequalities = And(Pair(false), Pair(true));
        if (which == 3)
            inequalities = Seq(Named("let"), Sp, F.Id("S"), F.Eq, S, Semi, Sp,
                Named("let"), Sp, F.Id("T"), F.Eq, Sub(Sum("j", d, Pow(At("a", "j"), 2)), Smul(Coeff(1, 2), Pow(F.Id("S"), 2))), Semi, Sp, inequalities);
        if (which == 2) inequalities = Imp(Eq(S, D(0)), inequalities);
        return All("A", F.Id("Type"), Seq(
            OpenBracket, Call("CStarAlgebra", A), CloseBracket, Sp,
            OpenBracket, Call("PartialOrder", A), CloseBracket, Sp,
            OpenBracket, Call("StarOrderedRing", A), CloseBracket, Sp,
            All("d", Nat(), Imp(Le(D(2), d), All("a", Arr(Fin(d), A), All("b", Arr(Fin(Sub(d, D(1))), A),
                Imp(factorHypothesis, inequalities)))))));
    }

    private static Formula OrderedFormula()
    {
        Formula A = F.Id("A"), d = F.Id("d"), z = F.Id("z");
        Formula list = Call("List.ofFn", Seq(Parenthesized(Seq(F.Id("i"), Colon, Fin(d))), Sp, Mapsto, Sp, Sub(z, At("a", "i"))));
        Formula body = Eq(Call("orderedDeriv", F.Id("a"), z), Sum("j", d, Call("List.prod", Call("List.eraseIdx", list, Call("val", F.Id("j"))))));
        return All("A", F.Id("Type"), Seq(OpenBracket, Call("Ring", A), CloseBracket, Sp,
            All("d", Nat(), All("a", Arr(Fin(d), A), All("z", A, body)))));
    }
    private static Formula FactorsFormula()
    {
        Formula A = F.Id("A"), d = F.Id("d"), z = F.Id("z");
        Formula indexType = Fin(Sub(d, D(1)));
        Formula mapping = Seq(Parenthesized(Seq(F.Id("k"), Colon, indexType)), Sp, Mapsto, Sp, Sub(z, At("b", "k")));
        Formula prod = Call("List.prod", Call("List.ofFn", mapping));
        Formula body = new Formula.Logic(Call("DerivFactors", d, F.Id("a"), F.Id("b")), FormulaLogicOperator.Iff,
            All("z", A, Eq(Call("orderedDeriv", F.Id("a"), z), Smul(d, prod))));
        return All("A", F.Id("Type"), Seq(OpenBracket, Call("Ring", A), CloseBracket, Sp,
            All("d", Nat(), All("a", Arr(Fin(d), A), All("b", Arr(Fin(Sub(d, D(1))), A), body)))));
    }
    private static Formula AFormula()
    {
        Formula x = Unit(0, 1), y = F.Id("y"), third = new Formula.Fraction(D(1), Cast(D(3)));
        return Eq(Seq(F.Id("a"), Colon, Arr(Fin(D(3)), Matrix2())), Seq(Bang, OpenBracket,
            Smul(third, Add(Smul(D(2), x), y)), Comma, Sp,
            Smul(third, Add(new Formula.Negate(x), y)), Comma, Sp,
            Smul(third, Sub(new Formula.Negate(x), Smul(D(2), y))), CloseBracket));
    }
    private static Formula BFormula() => Eq(Seq(F.Id("b"), Colon, Arr(Fin(D(2)), Matrix2())),
        Seq(Bang, OpenBracket, F.Id("u"), Comma, new Formula.Negate(F.Id("u")), CloseBracket));
}

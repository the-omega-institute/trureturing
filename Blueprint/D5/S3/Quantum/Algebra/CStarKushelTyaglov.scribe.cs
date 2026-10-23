using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CStarKushelTyaglovDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CStarKushelTyaglov.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/krishna2022cstarschoenberg");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cubic polynomial over two by two complex matrices refutes Krishna’s C*-algebraic conjecture.",
        H("CStarKushelTyaglov"), Blocks(
            Node("claimKushelTyaglov", "Krishna\u2019s Conjecture 2.4", new Formula.Logic(F.Id("claimKushelTyaglov"), FormulaLogicOperator.Iff, ClaimBody(3)),
                "Conjecture 2.4 (C*-algebraic Kushel-Tyaglov Conjecture), pp. 3–4: “Let 𝒜 be a C*-algebra, n∈ℕ\\{1} and let P(z) ≔ (z−a₁)(z−a₂)⋯(z−a_d) be a polynomial over 𝒜 with a₁, a₂, …, a_d ∈ 𝒜. Assume that P′ can be written as P′(z) ≔ d(z−b₁)⋯(z−b_{d−1}) on 𝒜 with b₁, b₂, …, b_{d−1} ∈ 𝒜. Then” the two inequalities displayed below. The printed n is read as d throughout. The encoding uses zero-based Fin d and Fin (d−1), complex scalar multiplication, star and the C*-order. It restricts the source to d≥2 and unital C*-algebras in Type with PartialOrder and StarOrderedRing; this weakens the assertion, so its negation refutes the source statement.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture is false", new Formula.Not(F.Id("claimKushelTyaglov")),
                "At degree three the matrices a and b satisfy the factorization hypothesis. The first inequality has right side minus left side equal to −67/27 times Matrix.single 0 0 1. Its first diagonal entry is negative, contradicting the C*-order.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("krishna-2022-cstar-kushel-tyaglov"),
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
    private static Formula Fin(Formula d) => Call("Fin", d);
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
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class CotfasDVGSDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/CotfasDVGS.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/QuantumContext/cotfas2026dvgs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The covariance uncertainty condition makes the trace-normalized mixed discrete Gaussian a density operator.",
        H("Cotfas discrete Gaussian positivity"), Blocks(
            Paragraph(Text("The indices are the integers from −s to s, with d = 2s + 1. "
                + "The covariance is a real positive-definite two by two matrix. "
                + "Matrix positivity uses the complex Hermitian order. Infinite lattice sums are tsums.")),
            Node("wigner", "W", "Continuous Gaussian Wigner function", WFormula(),
                "Page 2, Eq. (10): Wσ(q, p) = 2/(h√det σ) exp(−(2π/h) (q p) σ⁻¹ (q p)ᵀ). "
                    + "The two coordinates form the vector ![q, p]; dotProduct and Matrix.mulVec express the quadratic form.",
                AssessedProvenance.FromLiterature(Source)),
            Node("parity", "parity", "Discrete displaced parity", ParityFormula(),
                "Page 2, Eq. (18): “Π̃(n, k)ψ(m) = e^{(4πi/d) k(m−n)} ψ(2n − m).” "
                    + "The (m, j) entry is the coefficient of ψ(j), with centered modular reduction in the selected column. Page 2 fixes “the addition is modulo d.” ZMod.valMinAbs selects the unique representative in {−s, …, s} for d = 2s + 1.",
                AssessedProvenance.FromLiterature(Source)),
            Node("lattice", "wSum", "Signed Gaussian lattice sum", WSumFormula(),
                "Page 3, Eq. (22): W̃σ(n, k) = c′σ Σα,β (−1)^{αβ} "
                    + "Wσ((n + αd/2)√(h/d), (k + βd/2)√(h/d)). "
                    + "The expression omits only the scalar c′σ. Both lattice coordinates are integers, "
                    + "while every division inside the Wigner arguments is real division.",
                AssessedProvenance.FromLiterature(Source)),
            Node("matrix", "unnormalized", "Discrete Gaussian before normalization", UnnormalizedFormula(),
                "Page 3, Eq. (21): “Mixed DVGS - Inspired by the formulas (17) and (20), "
                    + "we have introduced in [21], for any d = 3, 5, 7, ..., the discrete version "
                    + "ρ̃_σ = Σ_{n,k=−s}^{s} W̃_σ(n, k) Π̃(n, k).” The two finite sums range over Finset.Icc (−s) s, "
                    + "and the real lattice weight is coerced to the complex scalars.",
                AssessedProvenance.FromLiterature(Source)),
            Node("density", "rhoTilde", "Trace normalization", RhoFormula(),
                "Page 3 describes c′κ as “a normalizing constant”. The normalized matrix is its "
                    + "unnormalized value multiplied by the inverse of its complex trace. "
                    + "The positivity proof establishes that this trace is nonzero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "Cotfas conjecture", Equal(N("claim"), Parenthesized(ClaimBody())),
                "Page 3, after Eq. (22): “As concern ρ̃_σ, we do not know if (11) is sufficient in order "
                    + "to have ρ̃_σ ≥ 0. Based on our numerical investigations, we conjecture that this is true.” "
                    + "Eq. (11) is “where the covariance matrix σ = (σ11 σ12; σ12 σ22), satisfying σ + i(0 1; −1 0) ≥ 0, is a real 2×2 symmetric positive-definite matrix.” The dimension is d = 2s + 1 with s ≥ 1. All positive h and all real positive-definite "
                    + "covariances satisfying the uncertainty condition are quantified. The conclusion also states trace one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", "The uncertainty condition suffices", ClaimBody(),
                "Scaling reduces the Planck parameter to d. Poisson summation identifies the exact matrix "
                    + "with twice a periodized Gaussian kernel. Its Gaussian Gram factor is positive semidefinite "
                    + "when det σ ≥ 1. A rank-one lower bound and theta nonvanishing give a strictly positive "
                    + "diagonal entry, hence a nonzero trace. The argument includes det σ = 1 and det σ > 1.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string text, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(text))), role);

    private static Formula N(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(N(owner), Dot, N(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) => Parenthesized(Seq(Typed(X(name), type), Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesThat(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtThan(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula RealType() => Seq(Mathbb, Grp(X("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(X("C")));
    private static Formula NatType() => Seq(Mathbb, Grp(X("N")));
    private static Formula IntType() => Seq(Mathbb, Grp(X("Z")));
    private static Formula FinTwo() => App(N("Fin"), D(2));
    private static Formula Covariances() => App(N("Matrix"), FinTwo(), FinTwo(), RealType());
    private static Formula Dim() => Add(Mul(D(2), Typed(X("s"), RealType())), D(1));
    private static Formula Indices() => App(Qualified("Finset", "Icc"), Negative(Typed(X("s"), IntType())), Typed(X("s"), IntType()));
    private static Formula RealCast(Formula value) => Typed(value, RealType());
    private static Formula ComplexCast(Formula value) => Typed(value, ComplexType());
    private static Formula Trace(Formula value) => App(Qualified("Matrix", "trace"), value);
    private static Formula PosSemidef(Formula value) => App(Qualified("Matrix", "PosSemidef"), value);
    private static Formula Sqrt(Formula value) => App(Qualified("Real", "sqrt"), value);
    private static Formula ExpReal(Formula value) => App(Qualified("Real", "exp"), value);
    private static Formula ExpComplex(Formula value) => App(Qualified("Complex", "exp"), value);
    private static Formula PiReal() => Qualified("Real", "pi");
    private static Formula Imaginary() => Qualified("Complex", "I");
    private static Formula Scalar(Formula coefficient, Formula value) => Seq(Parenthesized(coefficient), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Vector(Formula q, Formula p) => Seq(Bang, OpenBracket, q, Comma, Sp, p, CloseBracket);
    private static Formula State(string name) => App(N(name), X("s"), X("h"), X("sigma"));
    private static Formula Parameters(Formula body) => All("s", NatType(), All("h", RealType(), All("sigma", Covariances(), body)));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula TsumOver(string name, Formula type, Formula body) => App(N("tsum"), Fun(name, type, body));

    private static Formula WFormula()
    {
        var vector = Vector(X("q"), X("p"));
        var quadratic = App(N("dotProduct"), vector,
            App(Qualified("Matrix", "mulVec"), new Formula.Power(X("sigma"), Negative(D(1))), vector));
        var rhs = Mul(Div(D(2), Mul(X("h"), Sqrt(App(Qualified("Matrix", "det"), X("sigma"))))),
            ExpReal(Mul(Negative(Div(Mul(D(2), PiReal()), X("h"))), quadratic)));
        return All("h", RealType(), All("sigma", Covariances(), All("q", RealType(), All("p", RealType(),
            Equal(App(N("W"), X("h"), X("sigma"), X("q"), X("p")), rhs)))));
    }

    private static Formula UncertaintyBody()
    {
        var symplectic = Seq(Bang, Bang, OpenBracket, ComplexCast(D(0)), Comma, Sp, D(1), Semi, Sp, Negative(D(1)), Comma, Sp, D(0), CloseBracket);
        var map = App(Qualified("Matrix", "map"), X("sigma"), Fun("x", RealType(), ComplexCast(X("x"))));
        return PosSemidef(Add(map, Scalar(Imaginary(), symplectic)));
    }

    private static Formula ParityFormula()
    {
        var modulus = Add(Mul(D(2), X("s")), D(1));
        var residue = Typed(Sub(Mul(D(2), Typed(X("n"), IntType())), Typed(X("m"), IntType())), App(N("ZMod"), modulus));
        var red = App(Qualified("ZMod", "valMinAbs"), residue);
        var exponent = Div(Mul(Mul(Mul(Mul(D(4), PiReal()), Imaginary()), ComplexCast(Typed(X("k"), IntType()))),
            Sub(ComplexCast(Typed(X("m"), IntType())), ComplexCast(Typed(X("n"), IntType())))), Add(Mul(D(2), ComplexCast(X("s"))), D(1)));
        var rhs = Seq(N("if"), Sp, Equal(Typed(X("j"), IntType()), red), Sp, N("then"), Sp, ExpComplex(exponent), Sp, N("else"), Sp, D(0));
        return All("s", NatType(), All("n", Indices(), All("k", Indices(), All("m", Indices(), All("j", Indices(),
            Equal(App(N("parity"), X("s"), X("n"), X("k"), X("m"), X("j")), rhs))))));
    }

    private static Formula WSumFormula()
    {
        var z = X("z");
        var alpha = Seq(z, Dot, D(1));
        var beta = Seq(z, Dot, D(2));
        Formula Coordinate(string index, Formula lattice) => Mul(
            Add(RealCast(Typed(X(index), IntType())), Div(Mul(RealCast(lattice), Dim()), D(2))), Sqrt(Div(X("h"), Dim())));
        var rhs = TsumOver("z", Parenthesized(Seq(IntType(), Sp, Times, Sp, IntType())),
            Mul(new Formula.Power(RealCast(Negative(D(1))), Mul(alpha, beta)),
                App(N("W"), X("h"), X("sigma"), Coordinate("n", alpha), Coordinate("k", beta))));
        return Parameters(All("n", Indices(), All("k", Indices(),
            Equal(App(N("wSum"), X("s"), X("h"), X("sigma"), X("n"), X("k")), rhs))));
    }

    private static Formula UnnormalizedFormula() => Parameters(Equal(State("unnormalized"),
        SumOver("n", Indices(), SumOver("k", Indices(), Scalar(
            ComplexCast(App(N("wSum"), X("s"), X("h"), X("sigma"), X("n"), X("k"))),
            App(N("parity"), X("s"), X("n"), X("k")))))));

    private static Formula RhoFormula() => Parameters(Equal(State("rhoTilde"),
        Scalar(new Formula.Power(Parenthesized(Trace(State("unnormalized"))), Negative(D(1))), State("unnormalized"))));

    private static Formula ClaimBody() => All("s", NatType(), ImpliesThat(Leq(D(1), X("s")),
        All("h", RealType(), ImpliesThat(LtThan(D(0), X("h")), All("sigma", Covariances(),
            ImpliesThat(App(Qualified("Matrix", "PosDef"), X("sigma")),
                ImpliesThat(UncertaintyBody(), And(
                    PosSemidef(State("rhoTilde")), Equal(Trace(State("rhoTilde")), D(1))))))))));
}

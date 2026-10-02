using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class HigherAntibracketCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/manetti2016antibrackets");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n >= 2, the coefficients c_1^n, ..., c_n^n that express the higher Koszul bracket Phi^(n+1) through the operators rho_1, ..., rho_n are given by the closed formula conjectured by M. Manetti and G. Ricciardi (arXiv:1509.09032, Conjecture 2.4), and (-1)^n c_i^n > 0 for every n >= i >= 1, where c_1^1 = -1. The identity is the one of their Theorem 6.4, stated for linear endomorphisms of Q[x].",
        H("The closed form of the higher-antibracket coefficients"),
        Blocks(
            Node("phi", "The operators Phi^(m,i)", PhiFormula(),
                "Phi^(m,i) is the linear endomorphism of Q[x] sending x^i to x^(m-i)/(m-i)! and every other monomial to 0.",
                "phi", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("koszul", "The higher Koszul brackets", KoszulFormula(),
                "Phi^m is the alternating sum of the operators Phi^(m,i) with signs (-1)^(m-i), for i from 1 to m.",
                "koszul", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rho", "The operators rho_k", RhoFormula(),
                "For a linear endomorphism Psi of Q[x], rho_k(Psi) is the composition of (x^k/k! - x^(k+1) D/(k+1)!) with Psi, minus the composition of Psi with x D^(k+1)/(k+1)!, where D is the derivative of polynomials.",
                "rho", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("formula", "The conjectured coefficient", CoefficientFormula(),
                "The coefficient printed in the conjecture: (-1)^n times the product over j from 2 to i of (n(n-1) - (j-1)(j-2))/2, divided by the sum over h from 2 to n of h times the same product up to h times the product over j from h to n-1 of (1-j)(j+2)/2. Empty products are 1.",
                "formula", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "For every n >= 2, a sequence c satisfies Phi^(n+1) = c_1 rho_1^n Phi^1 + c_2 rho_1^(n-2) rho_2 Phi^1 + ... + c_n rho_n Phi^1 exactly when c_i equals the printed coefficient for 1 <= i <= n. For n = 1 the identity Phi^2 = c_1 rho_1 Phi^1 holds exactly when c_1 = -1. For every n >= 1, every solution c satisfies (-1)^n c_i > 0 for 1 <= i <= n. Here rho_1^(n-i) applies rho_1 n - i times. The paper proves that this identity has a unique solution and that the coefficients of its Theorem 2.3 are that solution, so the three parts are the formula of the conjecture for n >= 2 and its sign clause for n >= i >= 1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The closed form holds", Disp(F.Id("claim")),
                "Write an operator through its values on monomials and record the coefficient of x^d/d! in its value at x^s as the lattice point (d, s). Then rho_k sends (d, s) to alpha_k(d) (d + k, s) - C(s + k, k + 1) (d, s + k) with alpha_k(d) = C(d + k, k) - C(d + k, k + 1), and rho_i Phi^1 = (i, 1) - (0, i + 1). The two moves of rho_1 commute, so rho_1^t expands binomially along products of the step weights. The identity becomes n + 1 linear equations in c, one for each lattice point (d, n + 1 - d). Since alpha_1(2) = 0, the equations for d >= 3 form a triangular system in c_3, ..., c_n, and those for d = 0 and d = 1 then fix c_1 and c_2, which gives uniqueness. For c_i = (-1)^n (n+i-2)! / ((n-i)! 2^(i-1)) divided by (n-2)! (n+1)! / 2^(n-1), every equation reduces to the alternating binomial sum over i of (-1)^(M-i) C(M, i) C(i + a, b), which is C(a, b - M) for M <= b and 0 otherwise. The same sum shows that the printed product and denominator equal these factorial expressions for n >= 3; the case n = 2 is computed directly and gives c_1 = c_2 = 1/2, and for n = 1 the two equations give c_1 = -1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("manetti-ricciardi-2015-higher-antibracket-coefficients"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("antibracket-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Fact(Formula value) => Seq(Parenthesized(value), Bang);
    private static Formula Ite(Formula condition, Formula then, Formula otherwise) =>
        Call(F.Id("ite"), condition, then, otherwise);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula X() => F.Id("x");
    private static Formula Deriv() => Named(F.Id("D"));
    private static Formula Endo() => Call(F.Id("End"), Seq(Rat(), OpenBracket, X(), CloseBracket));
    private static Formula SumFrom(Formula index, Formula start, Formula stop, Formula body) =>
        Seq(F.Sum, Underscore, Grp(index, Eq, start), Caret, Grp(stop), Sp, body);
    private static Formula ProdFrom(Formula index, Formula start, Formula stop, Formula body) =>
        Seq(F.Prod, Underscore, Grp(index, Eq, start), Caret, Grp(stop), Sp, body);
    private static Formula Sign(Formula exponent) => Pow(Parenthesized(Seq(F.Minus, D(1))), exponent);
    private static Formula Between(Formula i, Formula n) => And(Le(D(1), i), Le(i, n));

    private static Formula PhiFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i"), s = F.Id("s");
        Formula value = Ite(Equal(s, i), Frac(Pow(X(), Minus(m, i)), Fact(Minus(m, i))), D(0));
        return Disp(All(m, Nat(), All(i, Nat(), All(s, Nat(),
            Equal(Call(F.Id("phi"), m, i, Pow(X(), s)), value)))));
    }

    private static Formula KoszulFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i");
        return Disp(All(m, Nat(), Equal(Call(F.Id("koszul"), m),
            SumFrom(i, D(1), m, Times(Sign(Minus(m, i)), Call(F.Id("phi"), m, i))))));
    }

    private static Formula RhoFormula()
    {
        Formula k = F.Id("k"), psi = Psi;
        Formula left = Parenthesized(Minus(Frac(Pow(X(), k), Fact(k)),
            Frac(Times(Pow(X(), Plus(k, D(1))), Deriv()), Fact(Plus(k, D(1))))));
        Formula right = Parenthesized(Frac(Times(X(), Pow(Deriv(), Plus(k, D(1)))), Fact(Plus(k, D(1)))));
        Formula body = Equal(Call(F.Id("rho"), k, psi),
            Minus(Seq(left, Sp, Circ, Sp, psi), Seq(psi, Sp, Circ, Sp, right)));
        return Disp(All(k, Nat(), All(psi, Endo(), body)));
    }

    private static Formula Factor(Formula n, Formula j) =>
        Frac(Minus(Times(n, Parenthesized(Minus(n, D(1)))),
            Times(Parenthesized(Minus(j, D(1))), Parenthesized(Minus(j, D(2))))), D(2));

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j"), h = F.Id("h");
        Formula numerator = Times(Sign(n), ProdFrom(j, D(2), i, Factor(n, j)));
        Formula tail = ProdFrom(j, h, Minus(n, D(1)),
            Frac(Times(Parenthesized(Minus(D(1), j)), Parenthesized(Plus(j, D(2)))), D(2)));
        Formula denominator = SumFrom(h, D(2), n,
            Times(Times(h, Parenthesized(ProdFrom(j, D(2), h, Factor(n, j)))), tail));
        return Disp(All(n, Nat(), All(i, Nat(),
            Equal(Call(F.Id("formula"), n, i), Frac(numerator, denominator)))));
    }

    private static Formula Identity(Formula n, Formula c)
    {
        Formula i = F.Id("i");
        Formula start = Call(F.Id("rho"), i, Call(F.Id("koszul"), D(1)));
        Formula term = Times(Sub(c, i), Seq(Pow(Sub(Named(F.Id("rho")), D(1)), Minus(n, i)), Parenthesized(start)));
        return Equal(Call(F.Id("koszul"), Plus(n, D(1))), SumFrom(i, D(1), n, term));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), c = F.Id("c");
        Formula sequences = new Formula.TypeArrow(Nat(), Rat());
        Formula solution = All(i, Nat(), Implies(Parenthesized(Between(i, n)),
            Equal(Sub(c, i), Call(F.Id("formula"), n, i))));
        Formula large = All(n, Nat(), Implies(Le(D(2), n),
            All(c, sequences, Iff(Identity(n, c), solution))));
        Formula one = All(c, sequences, Iff(Identity(D(1), c), Equal(Sub(c, D(1)), Seq(F.Minus, D(1)))));
        Formula sign = All(n, Nat(), Implies(Le(D(1), n), All(c, sequences, Implies(Parenthesized(Identity(n, c)),
            All(i, Nat(), Implies(Parenthesized(Between(i, n)), Lt(D(0), Times(Sign(n), Sub(c, i)))))))));
        Formula body = And(large, And(one, sign));
        return Disp(Iff(F.Id("claim"), body));
    }
}

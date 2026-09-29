using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TriangleInequalityL1RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/baumer2024trianglelocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inequality s_111(p) - 0.475 Delta_1(p) <= 0.289, which E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner (arXiv:2405.08939, eq. ineq_l1) state should hold for every distribution that is local in the triangle network, fails: a local model with four outcomes per party has Delta_1 = 0 and s_111 = 11/36.",
        H("A local counterexample to the triangle inequality ineq_l1"),
        Blocks(
            Node("type", "Outcome type", TypeFormula(),
                "The number of distinct outcomes among a, b, c: 1 for the type 111, 2 for the type 112 and 3 for the type 123. The three types contain 4, 36 and 24 outcome triples.",
                "outcomeType", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mean", "Mean over an outcome type", MeanFormula(),
                "M_X of the paper: the mean of p over the outcome triples of type m.",
                "typeMean", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("delta", "Asymmetry penalty", DeltaFormula(),
                "Delta_{l=1} of the paper: the absolute deviations of p from the mean of its outcome type, summed over the three types.",
                "deltaL1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The inequality ineq_l1", ClaimFormula(),
                "Eq. (ineq_l1) of the paper with its printed constants 0.475 and 0.289, for every distribution that is local in the triangle network in the sense of eq. (trilocal).",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A local distribution violating ineq_l1",
                Disp(new Formula.Not(F.Id("claim"))),
                "Let each source send one of the 24 orderings x = (x_1, x_2, x_3, x_4) of the four outcomes, uniformly, and let every party apply one rule f to its two sources in cyclic order: A = f(beta, gamma), B = f(gamma, alpha), C = f(alpha, beta). If x_1 or x_2 stands in one of the first two places of y, f(x, y) is whichever of them comes first in y; otherwise f(x, y) is x_1 if x_1 precedes x_2 in y, and x_3 if not. Cutting [0, 1] into 24 equal cells turns this into responses on [0, 1], and as for the fully symmetric model of the same paper the integral factorises over the cells, so p(a, b, c) is the number of source triples with outputs (a, b, c) divided by 24^3 = 13824. Sixteen kernel-checked counts over the 13824 triples give 1056 when a = b = c, 148 when exactly two outputs agree and 178 when all differ. So p is constant on each outcome type, every deviation from the type mean vanishes and Delta_1(p) = 0, while s_111(p) = 4 * 1056 / 13824 = 11/36 > 0.289.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("baumer-2024-triangle-inequality-l1"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("triangle-l1-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Fraction(byte[] numerator, byte[] denominator) =>
        Seq(Frac, Grp(D(numerator)), Grp(D(denominator)));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(byte n) => Call(F.Id("Fin"), D(n));
    private static Formula P(params Formula[] arguments) => new Formula.Apply(F.Id("p"), [.. arguments]);
    private static Formula Type(Formula a, Formula b, Formula c) => Call(F.Id("outcomeType"), a, b, c);

    private static Formula TypeFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula set = Seq(OpenBrace, a, Comma, Sp, b, Comma, Sp, c, CloseBrace);
        return Disp(Equal(Type(a, b, c), new Formula.Absolute(set)));
    }

    private static Formula MeanFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), m = F.Id("m");
        Formula triple = Seq(Open, a, Comma, Sp, b, Comma, Sp, c, Close);
        Formula cube = new Formula.Power(FinOf(4), D(3));
        Formula ofType = Equal(Type(a, b, c), m);
        Formula total = SumOver(Seq(triple, Sp, InMacro, Sp, cube, Comma, Sp, ofType), P(a, b, c));
        Formula size = new Formula.Absolute(Seq(OpenBrace, triple, Sp, InMacro, Sp, cube, Sp, Mid, Sp,
            ofType, CloseBrace));
        return Disp(Equal(Call(F.Id("typeMean"), F.Id("p"), m), Seq(Frac, Grp(total), Grp(size))));
    }

    private static Formula DeltaFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula deviation = new Formula.Absolute(Minus(
            Call(F.Id("typeMean"), F.Id("p"), Type(a, b, c)), P(a, b, c)));
        return Disp(Equal(Call(F.Id("deltaL1"), F.Id("p")),
            SumOver(a, SumOver(b, SumOver(c, deviation)))));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p");
        Formula left = Minus(Call(F.Id("s111"), p),
            Times(Fraction([4, 7, 5], [1, 0, 0, 0]), Call(F.Id("deltaL1"), p)));
        Formula bound = Rel(left, FormulaRelationOperator.LessThanOrEqual, Fraction([2, 8, 9], [1, 0, 0, 0]));
        Formula body = All("p", Seq(FinOf(4), Sp, To, Sp, FinOf(4), Sp, To, Sp, FinOf(4), Sp, To, Sp, Reals()),
            Implies(Call(F.Id("IsTriangleLocal"), p), bound));
        return Disp(Iff(F.Id("claim"), body));
    }
}

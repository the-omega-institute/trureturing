using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SpeyerUniformVarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform-matroid g-polynomials have Bernoulli factorizations and variance at least (d-1)/8.",
        H("Speyer Uniform Variance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("g"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformVariance.g"),
                H("g"),
                StatementSource.FromAuthor(Disp(All("n", Nat, All("d", Nat, Equal(Call("g", V("n"), V("d")), Seq(new Formula.Subscript(Sum, Seq(V("i"), Sp, InMacro, Sp, new Formula.Apply(Qualified("Finset", "Icc"), [new Formula.Number(1), Call("min", V("d"), Subtract(V("n"), V("d")))]))), Sp, Parenthesized(Multiply(Call("C", new Formula.Fraction(Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(Subtract(V("n"), V("i")), new Formula.Number(1))]), Colon, Sp, Real)), Multiply(Multiply(Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(V("d"), V("i"))]), Colon, Sp, Real)), Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(Subtract(V("n"), V("d")), V("i"))]), Colon, Sp, Real))), Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(V("i"), new Formula.Number(1))]), Colon, Sp, Real))))), new Formula.Power(Parenthesized(V("X")), V("i")))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Proposition 1.1, page 1: “For any n ≥ 2 and 1 ≤ d ≤ n − 1, the g-polynomial of the uniform matroid Uₙ,ᵈ is given by” the displayed factorial sum. Every subtraction inside a factorial is natural-number subtraction; the factorial values are cast to the reals. The Lean index interval is Finset.Icc 1 (min d (n-d))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("speyer-variance-eighth-unconditional"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformVariance.speyer_variance_eighth_unconditional"),
                H("speyer_variance_eighth_unconditional"),
                StatementSource.FromAuthor(Disp(All("n", Nat, All("d", Nat, Imp(And(Rel(new Formula.Number(2), FormulaRelationOperator.LessThanOrEqual, V("d")), Rel(Multiply(new Formula.Number(2), V("d")), FormulaRelationOperator.LessThanOrEqual, V("n"))), Rel(new Formula.Fraction(Parenthesized(Seq(Parenthesized(Seq(Subtract(V("d"), new Formula.Number(1)), Colon, Sp, Nat)), Colon, Sp, Real)), new Formula.Number(8)), FormulaRelationOperator.LessThanOrEqual, Call("sigmaSq", Call("g", V("n"), V("d"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The roots of the transported polynomial lie strictly below -1. Its logarithmic derivative at zero bounds the coefficient variance from below by (d-1)/8. Subtraction d-1 is performed in the natural numbers before casting. The bound holds when 2 ≤ d and 2*d ≤ n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("speyer-variance-tendsto"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformVariance.speyer_variance_tendsto"),
                H("speyer_variance_tendsto"),
                StatementSource.FromAuthor(Disp(All("d", new Formula.TypeArrow(Nat, Nat), Imp(And(new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, And(Rel(new Formula.Number(1), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("d"), [V("n")])), Rel(new Formula.Apply(V("d"), [V("n")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(Qualified("Nat", "div"), [V("n"), new Formula.Number(2)])))), V("atTop")]), Call("Tendsto", V("d"), V("atTop"), V("atTop"))), Call("Tendsto", LambdaFormula("n", Nat, Call("sigmaSq", Call("g", V("n"), new Formula.Apply(V("d"), [V("n")])))), V("atTop"), V("atTop")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For eventually admissible uniform-matroid ranks tending to infinity, the coefficient variances tend to infinity. Nat.div is natural-number division, so n/2 means the integer quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("g-bernoulli-factorization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformVariance.g_bernoulli_factorization"),
                H("g_bernoulli_factorization"),
                StatementSource.FromAuthor(Disp(All("n", Nat, All("d", Nat, Imp(And(Rel(new Formula.Number(2), FormulaRelationOperator.LessThanOrEqual, V("d")), Rel(Multiply(new Formula.Number(2), V("d")), FormulaRelationOperator.LessThanOrEqual, V("n"))), Seq(Exists, Sp, Parenthesized(Seq(V("m"), Colon, Sp, Nat)), Comma, Sp, Seq(Exists, Sp, Parenthesized(Seq(V("p"), Colon, Sp, new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))))), Comma, Sp, And(All("i", Call("Fin", V("m")), Rel(Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)), FormulaRelationOperator.MemberOf, new Formula.Apply(Qualified("Set", "Ioo"), [new Formula.Number(0), new Formula.Number(1)]))), Equal(Call("normalized", Call("g", V("n"), V("d"))), Multiply(V("X"), Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliPGF", Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/harper1967stirling")),
                Blocks(Paragraph(Text("The normalized Speyer polynomial is X times a product of Bernoulli probability-generating polynomials, with every parameter strictly between zero and one. This Speyer specialization is derived here from its negative real roots; Harper is cited for the Bernoulli method."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula LambdaFormula(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}

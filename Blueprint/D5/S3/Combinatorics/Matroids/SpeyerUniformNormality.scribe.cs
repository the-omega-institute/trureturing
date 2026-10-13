using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SpeyerUniformNormalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Growing uniform-matroid ranks satisfy both the central and local normal limit theorems.",
        H("Speyer Uniform Normality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("g"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g"),
                H("g"),
                StatementSource.FromAuthor(Disp(All("n", Nat, All("d", Nat, Equal(Call("g", V("n"), V("d")), Seq(new Formula.Subscript(Sum, Seq(V("i"), Sp, InMacro, Sp, new Formula.Apply(Qualified("Finset", "Icc"), [new Formula.Number(1), Call("min", V("d"), Subtract(V("n"), V("d")))]))), Sp, Parenthesized(Multiply(Call("C", new Formula.Fraction(Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(Subtract(V("n"), V("i")), new Formula.Number(1))]), Colon, Sp, Real)), Multiply(Multiply(Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(V("d"), V("i"))]), Colon, Sp, Real)), Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(Subtract(V("n"), V("d")), V("i"))]), Colon, Sp, Real))), Parenthesized(Seq(new Formula.Apply(Qualified("Nat", "factorial"), [Subtract(V("i"), new Formula.Number(1))]), Colon, Sp, Real))))), new Formula.Power(Parenthesized(V("X")), V("i")))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Proposition 1.1, page 1: “For any n ≥ 2 and 1 ≤ d ≤ n − 1, the g-polynomial of the uniform matroid Uₙ,ᵈ is given by” the displayed factorial sum. Every subtraction inside a factorial is natural-number subtraction; the factorial values are cast to the reals. The Lean index interval is Finset.Icc 1 (min d (n-d))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("speyer-variance-eighth-unconditional"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.speyer_variance_eighth_unconditional"),
                H("speyer_variance_eighth_unconditional"),
                StatementSource.FromAuthor(Disp(All("n", Nat, All("d", Nat, Imp(And(Rel(new Formula.Number(2), FormulaRelationOperator.LessThanOrEqual, V("d")), Rel(Multiply(new Formula.Number(2), V("d")), FormulaRelationOperator.LessThanOrEqual, V("n"))), Rel(new Formula.Fraction(Parenthesized(Seq(Parenthesized(Seq(Subtract(V("d"), new Formula.Number(1)), Colon, Sp, Nat)), Colon, Sp, Real)), new Formula.Number(8)), FormulaRelationOperator.LessThanOrEqual, Call("sigmaSq", Call("g", V("n"), V("d"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The roots of the transported polynomial lie strictly below -1. Its logarithmic derivative at zero bounds the coefficient variance from below by (d-1)/8. Subtraction d-1 is performed in the natural numbers before casting. The bound holds when 2 ≤ d and 2*d ≤ n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("speyer-variance-tendsto"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.speyer_variance_tendsto"),
                H("speyer_variance_tendsto"),
                StatementSource.FromAuthor(Disp(All("d", new Formula.TypeArrow(Nat, Nat), Imp(And(new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, And(Rel(new Formula.Number(1), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("d"), [V("n")])), Rel(new Formula.Apply(V("d"), [V("n")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(Qualified("Nat", "div"), [V("n"), new Formula.Number(2)])))), V("atTop")]), Call("Tendsto", V("d"), V("atTop"), V("atTop"))), Call("Tendsto", LambdaFormula("n", Nat, Call("sigmaSq", Call("g", V("n"), new Formula.Apply(V("d"), [V("n")])))), V("atTop"), V("atTop")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For eventually admissible uniform-matroid ranks tending to infinity, the coefficient variances tend to infinity. Nat.div is natural-number division, so n/2 means the integer quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("g-bernoulli-factorization"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.g_bernoulli_factorization"),
                H("g_bernoulli_factorization"),
                StatementSource.FromAuthor(Disp(All("n", Nat, All("d", Nat, Imp(And(Rel(new Formula.Number(2), FormulaRelationOperator.LessThanOrEqual, V("d")), Rel(Multiply(new Formula.Number(2), V("d")), FormulaRelationOperator.LessThanOrEqual, V("n"))), Seq(Exists, Sp, Parenthesized(Seq(V("m"), Colon, Sp, Nat)), Comma, Sp, Seq(Exists, Sp, Parenthesized(Seq(V("p"), Colon, Sp, new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))))), Comma, Sp, And(All("i", Call("Fin", V("m")), Rel(Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)), FormulaRelationOperator.MemberOf, new Formula.Apply(Qualified("Set", "Ioo"), [new Formula.Number(0), new Formula.Number(1)]))), Equal(Call("normalized", Call("g", V("n"), V("d"))), Multiply(V("X"), Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliPGF", Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/harper1967stirling")),
                Blocks(Paragraph(Text("The normalized Speyer polynomial is X times a product of Bernoulli probability-generating polynomials, with every parameter strictly between zero and one. Repeated differentiation in the Rodrigues identity gives the splitting of H. Reflection and reversal give the splitting of qAB, and positivity on [-1, infinity) puts its real roots below -1. Normalizing those factors gives the Bernoulli product; Harper is cited for the Bernoulli method."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.claim"),
                H("claim"),
                StatementSource.FromAuthor(Disp(IffFormula(V("claim"), All("d", new Formula.TypeArrow(Nat, Nat), Imp(new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, And(Rel(new Formula.Number(1), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("d"), [V("n")])), Rel(new Formula.Apply(V("d"), [V("n")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(Qualified("Nat", "div"), [V("n"), new Formula.Number(2)])))), V("atTop")]), Imp(Call("Tendsto", V("d"), V("atTop"), V("atTop")), And(Call("CLT", LambdaFormula("n", Nat, Call("g", V("n"), new Formula.Apply(V("d"), [V("n")])))), Call("LLT", LambdaFormula("n", Nat, Call("g", V("n"), new Formula.Apply(V("d"), [V("n")]))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Conjecture 4.8, page 13, states verbatim: If d = d(n) is a real function of n such that d(n) → +∞ as n → +∞, then the coefficient of Speyer’s g-polynomial gₙ,ᵈ₍ₙ₎(t), namely Sᵢ(n,d(n)), is asymptotically normal by local and central limit theorems. The encoding uses an integer-valued rank sequence d, the eventual standing conditions 1 ≤ d(n) and d(n) ≤ Nat.div n 2, and Tendsto d atTop atTop. CLT and LLT are the uniform epsilon-form conventions above. The g-polynomial is the literal factorial sum of Proposition 1.1. The floor in LLT is an integer floor; Nat.div is natural-number division."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.result"),
                H("result"),
                StatementSource.FromAuthor(Disp(V("claim"))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/zhangzhao2024speyer")),
                Blocks(Paragraph(Text("Every eventually admissible rank sequence tending to infinity satisfies both limits. The normalized coefficient law is a shifted Bernoulli sum, and the lower bound (d-1)/8 forces its variance to diverge. The general Bernoulli limit theorem then gives CLT and LLT. Bounded rank lies outside this claim."))),
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
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}

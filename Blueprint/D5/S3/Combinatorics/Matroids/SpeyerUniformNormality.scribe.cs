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

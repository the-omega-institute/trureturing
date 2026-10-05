using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class AlternatingTailUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two legal cuts remove two alternating blocks at every scale.", H("Alternating Tail Upper Bound"), Blocks(
        Describe.Lean(DescribeId.Create("pd-alternatingtailupper-alternating-tail-upper"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/AlternatingTailUpper.alternating_tail_upper"),
            H("Uniform upper bound including the neighboring endpoint"),
            StatementSource.FromAuthor(MainFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For epsilon zero or one, two odd palindromic suffix cuts remove two alternating binary blocks and preserve the endpoint bit. Their centers use odd parts nine and one. Induction repeats the construction and ends at the empty prefix or a singleton. PL is the true minimum number of nonempty palindrome factors, and val denotes the natural value of a finite index."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula MainFormula()
    {
        var length = Add(Call("sum", Call("range", Mul(D(2), V("k"))),
            Lam("j", N(), new Formula.Power(D(2), Add(Mul(D(2), V("j")), D(1))))), V("eps"));
        var word = Call("ofFn", Lam("i", Call("Fin", length), Call("upd", Call("val", V("i")))));
        return Disp(All("k", N(), All("eps", N(), Imp(Le(V("eps"), D(1)),
            Le(Call("PL", word), Add(Mul(D(2), V("k")), V("eps")))))));
    }
}

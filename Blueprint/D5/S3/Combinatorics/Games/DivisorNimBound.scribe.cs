using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every nonempty board of positive heaps, the Grundy value is at most twice the smallest heap.",
        H("The Sharper Sprague–Grundy Bound for Divisor Nim"),
        Blocks(Describe.Lean(
            DescribeId.Create("result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Games/DivisorNimBound.result"),
            H("Twice the smallest heap"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Write the distinguished heap as two to its valuation times a positive odd part. "
                + "A sufficiently large odd part is covered by the coarse ceiling. "
                + "For smaller odd parts the divisor-sensitive recurrence is bounded by the large-valuation "
                + "integer estimates or the finite valuation range. The remaining distinguished heaps "
                + "of sizes two, four, and eight satisfy direct bounds. Choose a smallest heap."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("tyagi-2026-divisor-nim-sharper-sg-bound"), ResolutionKind.Proved))),
        []));

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula ResultFormula()
    {
        var p = F.Id("P"); var m = F.Id("m"); var h = F.Id("h");
        var minimal = All("h", Nat(), Imp(Mem(h,p), Le(m,h)));
        var twice = new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, m);
        var conclusion = All("m",Nat(),Imp(Mem(m,p),Imp(minimal,Le(Call("grundy",p),twice))));
        return Disp(All("P",Call("Multiset",Nat()),
            Imp(Call("Positive",p),Imp(Ne(p,D(0)),conclusion))));
    }
}

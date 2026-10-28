using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FrobeniusCentralObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nontrivial proper malnormal subgroup forces every central element to be one.",
        H("Central elements and Frobenius complements"),
        Blocks(Describe.Lean(
            DescribeId.Create("frobenius-central-element"),
            DeclarationHandle.Create(
                "D5/S3/FiniteGroups/FrobeniusCentralObstruction.central_eq_one_of_frobenius"),
            H("A central element is the identity"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let H be a nontrivial proper subgroup whose intersection with every conjugate "
                + "by an element outside H is trivial. A central element z belongs to H: "
                + "otherwise conjugation by z leaves H unchanged and contradicts nontriviality. "
                + "Choose an element outside H. Centrality puts z in the intersection with "
                + "that element's conjugate of H, so z is the identity."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula g = F.Id("G"), h = F.Id("H"), z = F.Id("z"), x = F.Id("g");
        Formula conjugate = App(Q("Subgroup", "map"), App(Q("MulAut", "conj"), x), h);
        Formula malnormal = All("g", g, Imp(new Formula.Not(Member(x, h)),
            Equal(App(Q("Min", "min"), h, conjugate), Q("Bot", "bot"))));
        Formula central = All("g", g,
            Equal(new Formula.Binary(x, FormulaBinaryOperator.Multiply, z),
                new Formula.Binary(z, FormulaBinaryOperator.Multiply, x)));
        Formula body = Imp(new Formula.Relation(h, FormulaRelationOperator.NotEqual, Q("Bot", "bot")),
            Imp(new Formula.Relation(h, FormulaRelationOperator.NotEqual, Q("Top", "top")),
                Imp(malnormal, All("z", g, Imp(central, Equal(z, D(1)))))));
        return Disp(All("G", Seq(F.Id("Type"), Star),
            Seq(OpenBracket, App(F.Id("Group"), g), CloseBracket, Comma, Sp,
                All("H", App(F.Id("Subgroup"), g), body))));
    }

    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
}

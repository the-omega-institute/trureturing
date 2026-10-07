using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class RankProductADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A product potential bounds every accepted paired chunk word", H("A product potential bounds every accepted paired chunk word"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-rankproducta-a-endpoint-score-bound"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/RankProductA.a_endpoint_score_bound"),
                H("a_endpoint_score_bound"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"xs",Call("List",Tuple(Naturals(),Naturals())),Implies(Call("mem",F.Id("xs"),Call("accepts",Call("chunkEndpoint",D(6)))),AtMost(Call("chunkScore",F.Id("rankA"),Call("map",F.Id("snd"),F.Id("xs"))),Add(Call("chunkScore",F.Id("rankA"),Call("map",F.Id("fst"),F.Id("xs"))),D(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A forward induction retains the grouped reachable product states. A backward induction from the accepting endpoint retains the co-accessible masks. The integer potential inequalities telescope the score difference to at most one. The finite checks are reduced by the Lean kernel in seventeen separate endpoint-state blocks."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}

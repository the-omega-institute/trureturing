using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class EndpointAutomatonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A paired-digit endpoint automaton", H("A paired-digit endpoint automaton"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-endpointautomaton-endpointrows"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.endpointRows"),
                H("endpointRows"), StatementSource.FromAuthor(Disp(Seq(F.Id("endpointRows"),Colon,Call("List",Call("List",Tuple(Naturals(),Naturals(),Naturals())))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal seventeen rows list triples (first bit, second bit, destination). All entries of the transition relation are the triples printed in the Lean table; empty rows have no transitions."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-endpointautomaton-endpoint"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.endpoint"),
                H("endpoint"), StatementSource.FromAuthor(Disp(Seq(F.Id("endpoint"),Colon,Call("NFA",Tuple(Call("Fin",D(2)),Call("Fin",D(2))),Call("Fin",D(1,7)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The start set consists only of state 0. The accept set is {3,9,11}. For paired bits d, t is in step(q,d) exactly when (val(d.fst),val(d.snd),val(t)) occurs in endpointRows[val(q)], using the empty list for a missing row."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-endpointautomaton-movesfrom"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.movesFrom"),
                H("movesFrom"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"q",Naturals(),And(Equal(Call("movesFrom",F.Id("q"),D(0)),Call("singleton",Tuple(D(0),D(0),F.Id("q")))),Bind(FormulaQuantifier.ForAll,"width",Naturals(),Equal(Call("movesFrom",F.Id("q"),Add(F.Id("width"),D(1))),Call("flatMap",Function("t",Tuple(Naturals(),Naturals(),Naturals()),Call("map",Function("s",Tuple(Naturals(),Naturals(),Naturals()),Tuple(Add(Multiply(Call("first",F.Id("t")),Call("pow",D(2),F.Id("width"))),Call("first",F.Id("s"))),Add(Multiply(Call("second",F.Id("t")),Call("pow",D(2),F.Id("width"))),Call("second",F.Id("s"))),Call("third",F.Id("s")))),Call("movesFrom",Call("third",F.Id("t")),F.Id("width")))),Call("getD",F.Id("endpointRows"),F.Id("q"),F.Id("nil"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed equations give the literal recursion: movesFrom(q,0)=[(0,0,q)]; for width+1, concatenate over (x,y,t) in endpointRows.getD(q,[]) the mapped list [(x*2^width+a,y*2^width+b,s) | (a,b,s) in movesFrom(t,width)]. It is a recursion over the bit width, with both chunk values read most significant first."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-endpointautomaton-chunkendpoint"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.chunkEndpoint"),
                H("chunkEndpoint"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"width",Naturals(),Equal(Call("chunkEndpoint",F.Id("width")),Call("nfa",Call("start",F.Id("endpoint")),Call("accept",F.Id("endpoint")),Function("q",Call("Fin",D(1,7)),Function("d",Tuple(Naturals(),Naturals()),Call("setOf",Function("t",Call("Fin",D(1,7)),Call("mem",Tuple(Call("fst",F.Id("d")),Call("snd",F.Id("d")),Call("val",F.Id("t"))),Call("movesFrom",Call("val",F.Id("q")),F.Id("width")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("nfa(start,accept,step) is the NFA record constructor. setOf forms the set of states satisfying its predicate. The start and accept sets are exactly those of endpoint; only the alphabet and transition relation are regrouped."))), DescribeRole.Definition))));


    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
}

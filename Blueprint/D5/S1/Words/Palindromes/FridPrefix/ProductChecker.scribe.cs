using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class ProductCheckerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closure and potential tests for paired finite-state runs", H("Closure and potential tests for paired finite-state runs"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-productchecker-rawmember"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductChecker.rawMember"),
                H("rawMember"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"raw",Call("Array",Call("Array",Call("List",Naturals()))),Bind(FormulaQuantifier.ForAll,"q",Naturals(),Bind(FormulaQuantifier.ForAll,"p",Naturals(),Bind(FormulaQuantifier.ForAll,"s",Naturals(),Equal(Call("rawMember",F.Id("raw"),F.Id("q"),F.Id("p"),F.Id("s")),Call("contains",Call("getD",Call("getD",F.Id("raw"),F.Id("q"),F.Id("emptyArray")),F.Id("p"),F.Id("nil")),F.Id("s"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership uses exactly the grouped lists, with an empty array and empty list as defaults."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-productchecker-coremember"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductChecker.coreMember"),
                H("coreMember"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"core",Call("Array",Call("Array",Naturals())),Bind(FormulaQuantifier.ForAll,"q",Naturals(),Bind(FormulaQuantifier.ForAll,"p",Naturals(),Bind(FormulaQuantifier.ForAll,"s",Naturals(),Equal(Call("coreMember",F.Id("core"),F.Id("q"),F.Id("p"),F.Id("s")),Call("testBit",Call("getD",Call("getD",F.Id("core"),F.Id("q"),F.Id("emptyArray")),F.Id("p"),D(0)),F.Id("s"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bit at second rank state s is tested in the mask for endpoint q and first rank state p."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-productchecker-potential"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductChecker.potential"),
                H("potential"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"digits",Call("Array",Call("Array",Naturals())),Bind(FormulaQuantifier.ForAll,"q",Naturals(),Bind(FormulaQuantifier.ForAll,"p",Naturals(),Bind(FormulaQuantifier.ForAll,"s",Naturals(),Equal(Call("potential",F.Id("digits"),F.Id("q"),F.Id("p"),F.Id("s")),Subtract(Call("int",Call("mod",Call("shiftRight",Call("getD",Call("getD",F.Id("digits"),F.Id("q"),F.Id("emptyArray")),F.Id("p"),D(0)),Multiply(D(3),F.Id("s"))),D(8))),D(2))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("mod is natural remainder; shiftRight is the natural bit shift. The remainder is cast to Int before subtracting 2. All missing arrays use the zero default."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-productchecker-movescheck"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductChecker.movesCheck"),
                H("movesCheck"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"width",Naturals(),Bind(FormulaQuantifier.ForAll,"moves",Call("Array",Call("Array",Tuple(Naturals(),Naturals(),Naturals()))),Equal(Call("movesCheck",F.Id("width"),F.Id("moves")),Call("boolAnd",Call("eqBool",Call("size",F.Id("moves")),D(1,7)),Call("all",Call("range",D(1,7)),Function("q",Naturals(),Call("boolAnd",Call("all",Call("movesFrom",F.Id("q"),F.Id("width")),Function("t",Tuple(Naturals(),Naturals(),Naturals()),Call("contains",Call("getElemBang",F.Id("moves"),F.Id("q")),F.Id("t")))),Call("all",Call("getElemBang",F.Id("moves"),F.Id("q")),Function("t",Tuple(Naturals(),Naturals(),Naturals()),Call("contains",Call("movesFrom",F.Id("q"),F.Id("width")),F.Id("t"))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The expression is the Boolean conjunction of moves.size=17 and, for every q in range(17), both list-inclusion tests between moves[q]! and movesFrom(q,width). Inclusion tests use all and contains, so order and multiplicity are ignored."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-productchecker-isaccept"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductChecker.isAccept"),
                H("isAccept"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"q",Naturals(),Equal(Call("isAccept",F.Id("q")),Call("decide",Call("mem",F.Id("q"),Call("list",D(3),D(9),D(1,1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The endpoint accept states are exactly 3, 9 and 11."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-productchecker-rowcheck"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductChecker.rowCheck"),
                H("rowCheck"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"rank",F.Id("ChunkRank"),Bind(FormulaQuantifier.ForAll,"moves",Call("Array",Call("Array",Tuple(Naturals(),Naturals(),Naturals()))),Bind(FormulaQuantifier.ForAll,"raw",Call("Array",Call("Array",Call("List",Naturals()))),Bind(FormulaQuantifier.ForAll,"core",Call("Array",Call("Array",Naturals())),Bind(FormulaQuantifier.ForAll,"digits",Call("Array",Call("Array",Naturals())),Bind(FormulaQuantifier.ForAll,"q",Naturals(),Bind(FormulaQuantifier.ForAll,"p",Naturals(),Bind(FormulaQuantifier.ForAll,"s",Naturals(),Equal(Call("rowCheck",F.Id("rank"),F.Id("moves"),F.Id("raw"),F.Id("core"),F.Id("digits"),F.Id("q"),F.Id("p"),F.Id("s")),Call("boolAnd",Call("if",Call("isAccept",F.Id("q")),Call("boolAnd",Call("coreMember",F.Id("core"),F.Id("q"),F.Id("p"),F.Id("s")),Call("decide",AtMost(Call("potential",F.Id("digits"),F.Id("q"),F.Id("p"),F.Id("s")),D(1)))),F.Id("true")),Call("all",Call("getElemBang",F.Id("moves"),F.Id("q")),Function("t",Tuple(Naturals(),Naturals(),Naturals()),Call("boolAnd",Call("rawMember",F.Id("raw"),Call("third",F.Id("t")),Call("getD",Call("getD",Call("transitions",F.Id("rank")),F.Id("p"),F.Id("emptyArray")),Call("first",F.Id("t")),D(0)),Call("getD",Call("getD",Call("transitions",F.Id("rank")),F.Id("s"),F.Id("emptyArray")),Call("second",F.Id("t")),D(0))),Call("if",Call("coreMember",F.Id("core"),Call("third",F.Id("t")),Call("getD",Call("getD",Call("transitions",F.Id("rank")),F.Id("p"),F.Id("emptyArray")),Call("first",F.Id("t")),D(0)),Call("getD",Call("getD",Call("transitions",F.Id("rank")),F.Id("s"),F.Id("emptyArray")),Call("second",F.Id("t")),D(0))),Call("boolAnd",Call("coreMember",F.Id("core"),F.Id("q"),F.Id("p"),F.Id("s")),Call("decide",AtMost(Add(Call("potential",F.Id("digits"),F.Id("q"),F.Id("p"),F.Id("s")),Subtract(Call("getD",Call("getD",Call("weights",F.Id("rank")),F.Id("s"),F.Id("emptyArray")),Call("second",F.Id("t")),D(0)),Call("getD",Call("getD",Call("weights",F.Id("rank")),F.Id("p"),F.Id("emptyArray")),Call("first",F.Id("t")),D(0)))),Call("potential",F.Id("digits"),Call("third",F.Id("t")),Call("getD",Call("getD",Call("transitions",F.Id("rank")),F.Id("p"),F.Id("emptyArray")),Call("first",F.Id("t")),D(0)),Call("getD",Call("getD",Call("transitions",F.Id("rank")),F.Id("s"),F.Id("emptyArray")),Call("second",F.Id("t")),D(0)))))),F.Id("true"))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The expression is the literal Boolean test in Lean. If q accepts, it requires coreMember(q,p,s) and U(q,p,s)<=1. For every (x,y,t) in moves[q]!, let p1=transitions[p][x], s1=transitions[s][y], and gain=weights[s][y]-weights[p][x], using getD defaults 0. It requires rawMember(t,p1,s1). If coreMember(t,p1,s1), it additionally requires coreMember(q,p,s) and U(q,p,s)+gain<=U(t,p1,s1). Otherwise that last test is true."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-productchecker-groupcheck"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductChecker.groupCheck"),
                H("groupCheck"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"rank",F.Id("ChunkRank"),Bind(FormulaQuantifier.ForAll,"moves",Call("Array",Call("Array",Tuple(Naturals(),Naturals(),Naturals()))),Bind(FormulaQuantifier.ForAll,"raw",Call("Array",Call("Array",Call("List",Naturals()))),Bind(FormulaQuantifier.ForAll,"core",Call("Array",Call("Array",Naturals())),Bind(FormulaQuantifier.ForAll,"digits",Call("Array",Call("Array",Naturals())),Bind(FormulaQuantifier.ForAll,"q",Naturals(),Equal(Call("groupCheck",F.Id("rank"),F.Id("moves"),F.Id("raw"),F.Id("core"),F.Id("digits"),F.Id("q")),Call("all",Call("range",Call("size",Call("transitions",F.Id("rank")))),Function("p",Naturals(),Call("all",Call("getD",Call("getD",F.Id("raw"),F.Id("q"),F.Id("emptyArray")),F.Id("p"),F.Id("nil")),Function("s",Naturals(),Call("rowCheck",F.Id("rank"),F.Id("moves"),F.Id("raw"),F.Id("core"),F.Id("digits"),F.Id("q"),F.Id("p"),F.Id("s"))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each endpoint-state block checks every listed reachable pair of rank states. all returns a Boolean conjunction over a list. The seventeen blocks are proved by kernel reduction."))), DescribeRole.Definition))));



    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class MaskReachabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bit masks retain actual nondeterministic paths", H("Bit masks retain actual nondeterministic paths"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-maskreachability-maskstep"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/MaskReachability.maskStep"),
                H("maskStep"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"rows",Call("List",Call("List",Naturals())),Bind(FormulaQuantifier.ForAll,"mask",Naturals(),Bind(FormulaQuantifier.ForAll,"symbol",Naturals(),Equal(Call("maskStep",F.Id("rows"),F.Id("mask"),F.Id("symbol")),Call("foldl",Function("r",Naturals(),Function("q",Naturals(),Call("if",Call("testBit",F.Id("mask"),F.Id("q")),Call("bitOr",F.Id("r"),Call("getD",Call("getElemBang",F.Id("rows"),F.Id("q")),F.Id("symbol"),D(0))),F.Id("r")))),D(0),Call("range",Call("length",F.Id("rows")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("bitOr is bitwise natural OR. The fold enumerates every row index, adds its transition mask exactly when that source-state bit is present, and uses zero for missing transition entries."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-maskreachability-masknfa"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/MaskReachability.maskNFA"),
                H("maskNFA"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"rows",Call("List",Call("List",Naturals())),Bind(FormulaQuantifier.ForAll,"start",Naturals(),Equal(Call("maskNFA",F.Id("rows"),F.Id("start")),Call("nfa",Call("setOf",Function("q",Naturals(),Equal(Call("testBit",F.Id("start"),F.Id("q")),F.Id("true")))),F.Id("univ"),Function("q",Naturals(),Function("symbol",Naturals(),Call("setOf",Function("s",Naturals(),And(Less(F.Id("q"),Call("length",F.Id("rows"))),Equal(Call("testBit",Call("getD",Call("getD",F.Id("rows"),F.Id("q"),F.Id("nil")),F.Id("symbol"),D(0)),F.Id("s")),F.Id("true"))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All states accept in this auxiliary path automaton. An edge requires q<rows.length and the destination bit of rows[q][symbol] to be present."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-maskreachability-mask-path"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/MaskReachability.mask_path"),
                H("mask_path"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"rows",Call("List",Call("List",Naturals())),Bind(FormulaQuantifier.ForAll,"w",Call("List",Naturals()),Bind(FormulaQuantifier.ForAll,"start",Naturals(),Bind(FormulaQuantifier.ForAll,"q",Naturals(),Implies(Equal(Call("testBit",Call("foldl",Call("maskStep",F.Id("rows")),F.Id("start"),F.Id("w")),F.Id("q")),F.Id("true")),Bind(FormulaQuantifier.Exists,"s",Naturals(),And(Equal(Call("testBit",F.Id("start"),F.Id("s")),F.Id("true")),Call("Nonempty",Call("Path",Call("maskNFA",F.Id("rows"),F.Id("start")),F.Id("s"),F.Id("q"),F.Id("w")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A bit that survives a full word has an actual path from an initial bit. The proof reconstructs a predecessor through each bitwise-OR transition."))), DescribeRole.Theorem))));


    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}

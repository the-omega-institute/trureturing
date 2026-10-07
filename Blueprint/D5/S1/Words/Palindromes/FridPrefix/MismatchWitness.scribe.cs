using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class MismatchWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mismatch path constructs reflected unequal Fibonacci letters", H("A mismatch path constructs reflected unequal Fibonacci letters"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-mismatchwitness-badcoordinates"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/MismatchWitness.badCoordinates"),
                H("badCoordinates"), StatementSource.FromAuthor(Disp(Seq(F.Id("badCoordinates"),Colon,Call("Array",Tuple(Naturals(),Naturals(),Integers(),Integers()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal 138 tuples contain previous-digit masks, comparison flags, and the two signed Fibonacci carry coordinates. The proof verifies every permitted transition against these coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-mismatchwitness-mismatch-witness"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/MismatchWitness.mismatch_witness"),
                H("mismatch_witness"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"symbols",Call("List",Naturals()),Implies(And(Bind(FormulaQuantifier.ForAll,"a",Naturals(),Implies(Call("mem",F.Id("a"),F.Id("symbols")),Less(F.Id("a"),D(4)))),Equal(Call("hasAccept",Call("foldl",Call("maskStep",F.Id("badRows")),F.Id("badStart"),F.Id("symbols")),F.Id("badAccept")),F.Id("true"))),Bind(FormulaQuantifier.Exists,"U",Call("List",Call("Fin",D(2))),Bind(FormulaQuantifier.Exists,"V",Call("List",Call("Fin",D(2))),And(Equal(Call("length",F.Id("U")),Call("length",F.Id("symbols"))),And(Equal(Call("length",F.Id("V")),Call("length",F.Id("symbols"))),And(Call("NoAdjacentOnes",F.Id("U")),And(Call("NoAdjacentOnes",F.Id("V")),And(Call("NoAdjacentOnes",Call("map",Function("a",Naturals(),Call("ofNat",D(2),Call("div",F.Id("a"),D(2)))),F.Id("symbols"))),And(Call("NoAdjacentOnes",Call("map",Function("a",Naturals(),Call("ofNat",D(2),F.Id("a"))),F.Id("symbols"))),And(AtMost(Call("fst",Call("fibPair",Call("map",Function("a",Naturals(),Call("ofNat",D(2),Call("div",F.Id("a"),D(2)))),F.Id("symbols")))),Call("fst",Call("fibPair",F.Id("U")))),And(Less(Call("fst",Call("fibPair",F.Id("U"))),Call("fst",Call("fibPair",Call("map",Function("a",Naturals(),Call("ofNat",D(2),F.Id("a"))),F.Id("symbols"))))),And(AtMost(Call("fst",Call("fibPair",Call("map",Function("a",Naturals(),Call("ofNat",D(2),Call("div",F.Id("a"),D(2)))),F.Id("symbols")))),Call("fst",Call("fibPair",F.Id("V")))),And(Less(Call("fst",Call("fibPair",F.Id("V"))),Call("fst",Call("fibPair",Call("map",Function("a",Naturals(),Call("ofNat",D(2),F.Id("a"))),F.Id("symbols"))))),And(Equal(Add(Call("fst",Call("fibPair",Call("map",Function("a",Naturals(),Call("ofNat",D(2),Call("div",F.Id("a"),D(2)))),F.Id("symbols")))),Call("fst",Call("fibPair",Call("map",Function("a",Naturals(),Call("ofNat",D(2),F.Id("a"))),F.Id("symbols"))))),Add(Add(Call("fst",Call("fibPair",F.Id("U"))),Call("fst",Call("fibPair",F.Id("V")))),D(1))),NotEqual(Call("getLastD",F.Id("U"),D(0)),Call("getLastD",F.Id("V"),D(0)))))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("X maps each paired symbol a to Fin.ofNat(2,a div 2), and Y maps it to Fin.ofNat(2,a). div is natural division. The two constructed canonical words U,V lie inside [value(X),value(Y)), their positions sum to value(X)+value(Y)-1, and their last digits differ. getLastD uses zero for an empty word."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}

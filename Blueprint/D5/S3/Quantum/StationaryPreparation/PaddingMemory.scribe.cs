using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingMemoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite padding memory and transition coordinates.",
        H("Finite Padding Memory"),
        Blocks(
            Paragraph(Text("For a finite index type I and a capacity function c:I to Nat, TailBox(c) contains bounded tail coordinates. PositiveTail(c) removes the all-zero tail, and PaddingMemory(H,c)=Option(PositiveTail(c) x Fin(H+1)) is the finite memory used by the padding construction.")),
            Theorem("padding-cardinality", "padding_memory_card", "The padding memory has exact cardinality", PaddingCardinalityFormula,
                "Removing the all-zero tail and adjoining the None sink gives the displayed product-minus-H count."),
            Theorem("occupation-cardinality", "occupation_memory_card", "Occupation memory has product-minus-head cardinality",
                All("A", Id("Type"), Imp(And(Call("Fintype", A), Call("DecidableEq", A)),
                    All("a", Multi, All("q", A, Eq(Card(Call("OccupationMemory", Id("a"), Id("q"))),
                        Sub(ProductAt("i", A, Add(Call("count", Id("a"), Id("i")), D(1))), Call("count", Id("a"), Id("q")))))))),
                "Choosing a letter of maximum count makes this count the product minus the maximum. The sink exists even when every count is zero."),
            Theorem("maximal-head", "maximal_head_exists", "A head of maximum count exists",
                AlphabetContext(All("a", Multi, Exists("q", A,
                    Eq(Call("count", Id("a"), Id("q")), Call("maxCount", Id("a")))))),
                "For nonempty A, maxCount(a) is the supremum over all i:A of count(a,i). The exact memory equivalence uses this equality to label the memory by Fin of the product-minus-maximum dimension."))));

    private const string Prefix = "D5/S3/Quantum/StationaryPreparation/PaddingMemory.";
    private static Formula A => Id("A");
    private static Formula I => Id("I");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Multi => Call("Multiset", A);
    private static Formula PaddingCardinalityFormula => IndexContext(
        All("H", N, All("c", Function(I, N), Eq(Card(Call("PaddingMemory", Id("H"), Id("c"))),
            Sub(Mul(Add(Id("H"), D(1)), ProductAt("i", I, Add(Call("c", Id("i")), D(1)))), Id("H"))))));
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Function(Formula domain, Formula codomain) => Call("Function", domain, codomain);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula ProductAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(F.Prod, Seq(Id(name), Colon, domain)), Grp(body));
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] values) => values.Reverse().Aggregate((right, left) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula IndexContext(Formula body) => All("I", Id("Type"), Imp(Call("Fintype", I), body));
    private static Formula AlphabetContext(Formula body) => All("A", Id("Type"), Imp(And(Call("Fintype", A), Call("DecidableEq", A), Call("Nonempty", A)), body));
    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string text) => Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}

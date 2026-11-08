using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenMinpolyRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjecture B.1 for literal diagram algebras", H("Conjecture B.1 for literal diagram algebras"), Blocks(
            Paragraph(Text("The coefficient field is C and the element is the negative sum h(C,n) of all n-1 standard generators. The multiplication is actual path concatenation of noncrossing matching diagrams, with every internal loop assigned zero. The definition below preserves the original universal quantifier. The degree-57 monic integer annihilator is transported through the exact generator action to the complex diagram algebra. Minpoly minimality gives degree at most 57, contradicting the conjectured value 81 at n=9. No faithful-representation assumption is used.")),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim"),
                H("claim"), StatementSource.FromAuthor(Disp(Iff(Id("claim"), All("n", Id("Nat"), Imp(Call("AtLeast", Id("n"), Num(2)), Equal(Call("RationalCast", Call("natDegree", Call("minpoly", Id("Complex"), Call("h", Id("Complex"), Id("n"))))), Call("Divide", Call("Add", Call("Power", Num(3), Call("Divide", Call("Add", Id("n"), Num(1)), Num(2))), Call("Multiply", Call("Power", Call("NegativeOne"), Id("n")), Call("Power", Num(3), Call("Divide", Call("Subtract", Id("n"), Num(1)), Num(2))))), Num(2)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The powers use natural-number exponents with natural division by two; the outer equality is in Q."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result"),
                H("result"), StatementSource.FromAuthor(Disp(Call("Not", Id("claim")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The integer Horner certificate, the literal diagram transition law, and the unit diagram yield p(h_9)=0. The polynomial is monic of degree 57, so minpoly has degree at most 57<81."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}

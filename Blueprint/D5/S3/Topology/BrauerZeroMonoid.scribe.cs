using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class BrauerZeroMonoidDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Loop-zero matching monoid", H("Loop-zero matching monoid"), Blocks(
            Paragraph(Text("None is the absorbing zero; some(d) is a literal fixed-point-free boundary involution. Multiplication is some(composite(d,e)) when the internal loop count is zero and is none otherwise. The unit is the identity through-strand matching. These definitions include zero strands.")),
            Describe.Lean(DescribeId.Create("zeromatching"), DeclarationHandle.Create("D5/S3/Topology/BrauerZeroMonoid.ZeroMatching"),
                H("ZeroMatching"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), Equal(Call("ZeroMatching", Id("n")), Call("Option", Call("Matching", Call("Boundary", Id("n")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The carrier adjoins one absorbing zero to all matchings."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zeromatchingmonoid"), DeclarationHandle.Create("D5/S3/Topology/BrauerZeroMonoid.zeroMatchingMonoid"),
                H("zeroMatchingMonoid"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), Equal(Call("zeroMatchingMonoid", Id("n")), Call("MonoidWithZeroStructure", Call("ZeroMatching", Id("n")), Call("LoopZeroProduct", Id("n")), Call("Some", Call("identityMatching", Id("n"))), Id("None")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The product has the displayed loop test. Pairing associativity and the loop cocycle prove associativity; the identity creates no internal loops."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("some-mul-some"), DeclarationHandle.Create("D5/S3/Topology/BrauerZeroMonoid.some_mul_some"),
                H("some_mul_some"), StatementSource.FromAuthor(Disp(All("N", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("N"))), All("e", Call("Matching", Call("Boundary", Id("N"))), Equal(Call("Multiply", Call("Some", Id("d")), Call("Some", Id("e"))), Call("If", Equal(Call("internalLoopCount", Id("d"), Id("e")), Num(0)), Call("Some", Call("composite", Id("d"), Id("e"))), Id("None")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The displayed product is the MonoidWithZero multiplication, not an additional operation."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}

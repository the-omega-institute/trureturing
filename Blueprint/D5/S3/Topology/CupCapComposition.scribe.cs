using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CupCapCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator paths and internal components", H("Generator paths and internal components"), Blocks(
            Paragraph(Text("Top ports are (false,j) and (false,j+1), written A and B. A generator retains their exterior cup and reconnects the partners of the sewn inputs. Explicit paths in the actual half-edge gluing prove the formula, without imposing a representation or replacing the algebra. When the inputs are paired, their four glued half-edges form a component with no outer endpoint; otherwise every half-edge has an explicit path to the outer boundary.")),
            Describe.Lean(DescribeId.Create("reconnected"), DeclarationHandle.Create("D5/S3/Topology/CupCapComposition.reconnected"),
                H("reconnected"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("j", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), Imp(Call("Less", Call("Add", Id("j"), Num(1)), Id("n")), All("x", Call("Boundary", Id("n")), Equal(Call("reconnected", Id("j"), Id("d"), Id("x")), Call("If", Equal(Id("x"), Call("Pair", Id("False"), Id("j"))), Call("Pair", Id("False"), Call("Add", Id("j"), Num(1))), Call("If", Equal(Id("x"), Call("Pair", Id("False"), Call("Add", Id("j"), Num(1)))), Call("Pair", Id("False"), Id("j")), Call("If", Equal(Call("mate", Id("d"), Id("x")), Call("Pair", Id("False"), Id("j"))), Call("mate", Id("d"), Call("Pair", Id("False"), Call("Add", Id("j"), Num(1)))), Call("If", Equal(Call("mate", Id("d"), Id("x")), Call("Pair", Id("False"), Call("Add", Id("j"), Num(1)))), Call("mate", Id("d"), Call("Pair", Id("False"), Id("j"))), Call("mate", Id("d"), Id("x")))))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The two generator outputs are paired directly. All other outputs follow the old matching, except for reconnecting the two old partners."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("composite-cupcap-mate"), DeclarationHandle.Create("D5/S3/Topology/CupCapComposition.composite_cupcap_mate"),
                H("composite_cupcap_mate"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("j", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), Imp(Call("Less", Call("Add", Id("j"), Num(1)), Id("n")), All("x", Call("Boundary", Id("n")), Equal(Call("mate", Call("composite", Call("cupcapMatching", Id("j")), Id("d")), Id("x")), Call("reconnected", Id("j"), Id("d"), Id("x")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The reconstructed partner is distinct from the starting endpoint and lies in its glued component. Completeness of the actual endpoint pairing identifies it with composite."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internalloopcount-cupcap-zero"), DeclarationHandle.Create("D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_zero"),
                H("internalLoopCount_cupcap_zero"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("j", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), Imp(Call("Less", Call("Add", Id("j"), Num(1)), Id("n")), Imp(Call("Not", Equal(Call("mate", Id("d"), Call("Pair", Id("False"), Id("j"))), Call("Pair", Id("False"), Call("Add", Id("j"), Num(1))))), Equal(Call("internalLoopCount", Call("cupcapMatching", Id("j")), Id("d")), Num(0))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every tagged half-edge reaches an exposed endpoint, so the internal-component subtype is empty."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internalloopcount-cupcap-pos"), DeclarationHandle.Create("D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_pos"),
                H("internalLoopCount_cupcap_pos"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("j", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), Imp(Call("Less", Call("Add", Id("j"), Num(1)), Id("n")), Imp(Equal(Call("mate", Id("d"), Call("Pair", Id("False"), Id("j"))), Call("Pair", Id("False"), Call("Add", Id("j"), Num(1)))), Call("Positive", Call("internalLoopCount", Call("cupcapMatching", Id("j")), Id("d")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The paired input component is isolated by a component-invariant patch coloring, providing an element of the finite internal-component subtype."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internalloopcount-cupcap-eq-zero-iff"), DeclarationHandle.Create("D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_eq_zero_iff"),
                H("internalLoopCount_cupcap_eq_zero_iff"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("j", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), Imp(Call("Less", Call("Add", Id("j"), Num(1)), Id("n")), Iff(Equal(Call("internalLoopCount", Call("cupcapMatching", Id("j")), Id("d")), Num(0)), Call("Not", Equal(Call("mate", Id("d"), Call("Pair", Id("False"), Id("j"))), Call("Pair", Id("False"), Call("Add", Id("j"), Num(1)))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The two directions give the exact zero-loop test used by the sparse generator action."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowRegisterProgramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fixed acquisition and handoff program.",
        H("One fixed acquisition and handoff program"),
        Blocks(
            Paragraph(Text("The finite control is the disjoint union of the packed acquisition control and the four-register control. The first actual packed completion enters register transfer after a paid read. All instructions remain local finite-symbol actions.")),
            Paragraph(Text("The first completion agrees with the packed run at every earlier prefix. Extending the program changes no earlier source acquisition state. Fixed code length and finite control do not depend on the supplied number or height.")),
            Describe.Lean(DescribeId.Create("first-done-lift"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterProgram.first_done_lift"), H("first done lift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: first_done_lift (c : Configuration) (T : \u2115) (hc : (PhysicalWindowContinuation.run c T).control=.done) : \u2203 s\u2264T,run (base c) s=base (PhysicalWindowContinuation.run c T) \u2227 \u2200 n \u2264 s, run (base c) n=base (PhysicalWindowContinuation.run c n)"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterComposition"))]));
}

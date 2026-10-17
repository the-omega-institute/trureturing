using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowRegisterResourcesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal canonical endpoint and joint resources.",
        H("Literal canonical endpoint and joint resources"),
        Blocks(
            Paragraph(Text("RegisterRep requires a head at origin, literal little-endian bits with no high zero padding except a single zero bit for zero, the exact natural value, the explicit end marker and blanks elsewhere. It is a tape relation, rather than an arithmetic service premise.")),
            Paragraph(Text("The persistent charge covers all eight tracks, the finite control and fixed code, supplied input and origin cells, every visited cell and every head description. Every prefix of one run is bounded through the same common head interval.")),
            Describe.Lean(DescribeId.Create("register-rep"), DeclarationHandle.Create("D5/S0/Computability/WindowRegisterResources.register_rep"), H("register rep"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: register_rep (w : List Window) (e : Bool) (j : Lane) : RegisterRep (registerEnd w e) j (bitValue (select j) (Original.finalColumns w e))"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-bound"), DeclarationHandle.Create("D5/S0/Computability/WindowRegisterResources.charged_bound"), H("charged bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: charged_bound (w : List Window) (e : Bool) (T : \u2115) (hf : \u2200 n \u2264 T, \u2200 t, 0 \u2264 (run (initial w e) n).head t \u2227 (run (initial w e) n).head t \u2264 3*w.length+6) : \u2200 n \u2264 T, charged w e n \u2264 (code.length + Fintype.card State + 80*(Fintype.card Symbol+1)) * (w.length+1)"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/WindowRegisterProgram"))]));
}

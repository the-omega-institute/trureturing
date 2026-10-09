using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class QuantumMaxFlowMinCutDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/gesmundo2025bridge");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(params Formula[] names) => Seq(Operatorname, Grp(names));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "QuantumMaxFlowMinCut supplies the width-three bridge max-flow proof.",
        H("QuantumMaxFlowMinCut"), Blocks(
            Paragraph(Text("Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.")),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowmincut-claim"),
                DeclarationHandle.Create(Owner + ".claim"),
                H("claim"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Conjecture 1.4, page 6: “Let (a, b), (a′, b′) ∈ U_w ∪ V_w ∪ W_w. Then” followed by “QMaxFlow = QMinCut = min{a·b′, a′·b}” with the bridge-diagram arguments. Conjecture 3.14 repeats this on page 19. Conjecture 3.15, page 19: “Let (a, b), (a′, b′) ∈ U_3 ∪ V_3 ∪ W_3. Then” followed by “QMinCut = QMaxFlow = min{a′b, ab′}” at width three. The parameters are positive natural dimensions, and (a,b,c,d)=(a,b,a′,b′). The source region is exactly a ≤ b and a*a+b*b ≤ 3*a*b: its larger ratio endpoint is (3+√5)/2, as derived in the cited note. Both equalities are retained."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowmincut-result"),
                DeclarationHandle.Create(Owner + ".result"),
                H("result"), StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The unconditional width-three settlement combines a rational cyclic shift construction, short and long reservoir Schur complements, scalar extension to complex matrices, and castling deficit preservation followed by strong induction on b+d. Proposition 3.18 of the source derives Conjecture 1.4 at every w≥3 from this case; that general-width implication is a literature reading, not a theorem formalized here."))),
                DescribeRole.Theorem))));

    private static Formula Statement0() =>
        Seq(Qualified(F.Id("QuantumMaxFlowMinCut"), Dot, F.Id("claim")), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp,
        Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("a"), Sp, To, Sp, F.Id("a"), Sp, Leq, Sp,
        F.Id("b"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("c"), Sp, To, Sp, F.Id("c"), Sp, Leq, Sp, F.Id("d"), Sp, To,
        Sp, F.Id("a"), Sp, Cdot, Sp, F.Id("a"), Sp, Plus, Sp, F.Id("b"), Sp, Cdot, Sp, F.Id("b"), Sp, Leq, Sp, D(3),
        Sp, Cdot, Sp, F.Id("a"), Sp, Cdot, Sp, F.Id("b"), Sp, To, Sp, F.Id("c"), Sp, Cdot, Sp, F.Id("c"), Sp, Plus,
        Sp, F.Id("d"), Sp, Cdot, Sp, F.Id("d"), Sp, Leq, Sp, D(3), Sp, Cdot, Sp, F.Id("c"), Sp, Cdot, Sp, F.Id("d"),
        Sp, To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMaxFlow")), Sp, F.Id("a"), Sp, F.Id("b"), Sp,
        F.Id("c"), Sp, F.Id("d"), Sp, Eq, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMinCut")), Sp,
        F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Land, Sp, Qualified(F.Id("QuantumMaxFlowBound"),
        Dot, F.Id("QMinCut")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Eq, Sp, F.Id("min"),
        Sp, Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp,
        F.Id("c"))))));

    private static Formula Statement1() =>
        Qualified(F.Id("QuantumMaxFlowMinCut"), Dot, F.Id("claim"));

}

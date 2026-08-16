using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.OrbitClosure;

internal sealed class CompactConnectedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var orbitClosure = Seq(
            Operatorname, Grp(F.Id("cl")), Open,
            Operatorname, Grp(F.Id("range")), Open,
            F.Id("t"), Mapsto, Phi, Open, F.Id("t"), Comma,
            Xi, Underscore, Grp(D(0)), Close, Close, Close);
        var conclusion = new Formula.Logic(
            Seq(Operatorname, Grp(F.Id("Compact")), Open, orbitClosure, Close),
            FormulaLogicOperator.And,
            Seq(Operatorname, Grp(F.Id("Connected")), Open, orbitClosure, Close));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Continuous real-orbit closures in compact metric spaces are compact and connected.",
            H("Compact Connected Orbit Closures"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("orbit-closure-compact-and-connected"),
                    DeclarationHandle.Create(
                        "D5/S1/Dynamics/OrbitClosure/CompactConnected."
                        + "orbit_closure_is_compact_and_connected"),
                    H("A continuous real-orbit closure is compact and connected"),
                    StatementSource.FromAuthor(Disp(conclusion)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let the orbit of xi0 be the range of t mapped to flow(t, xi0), "
                            + "where flow is continuous on the product of the real line and W. "
                            + "Its closure is closed in compact W, hence compact.")),
                        Paragraph(Text(
                            "The real line is connected. Its continuous orbit image is therefore "
                            + "connected, and connectedness is preserved by taking closure.")),
                        Paragraph(Text(
                            "Pinned Mathlib provides isConnected_range, IsConnected.closure, and "
                            + "IsClosed.isCompact. No single searched declaration combines both "
                            + "conclusions, so the proof is their thinnest direct composition."))),
                    DescribeRole.Theorem))));
    }
}

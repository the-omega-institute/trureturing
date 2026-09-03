using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class FiniteStableDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite state space reaches its complete prediction relation at a finite depth.",
        H("Finite Stable Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-state-has-stable-depth"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/FiniteStableDepth."
                        + "finite_state_has_stable_depth"),
                H("Finite states have a stable prediction depth"),
                StatementSource.FromAuthor(StableDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite state type, J the type of selected local interfaces, "
                            + "F a deterministic self-map, and q_i the readout at interface i. "
                            + "The existing jointObservation q is the source's joint readout q_J.")),
                    Paragraph(Text(
                        "At depth m, finiteHorizonKernel is the equality relation induced by "
                            + "the indexed readout word through times zero to m. The relation on "
                            + "the right is the equality kernel of completeItinerary, which records "
                            + "the same indexed readouts at every natural time.")),
                    Paragraph(Text(
                        "The theorem asserts exactly one conclusion: some natural depth makes "
                            + "these two relations equal. Repository declaration "
                            + "finite_horizon_stabilizes_at_completionDepth supplies that equality "
                            + "after the finite state instance is made available; no second "
                            + "readout, relation, or stabilization proof is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula StableDepthFormula()
    {
        Formula states = F.Id("X");
        Formula interfaces = F.Id("J");
        Formula outputs = Seq(F.Id("O"), Underscore, F.Id("i"));
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula depth = F.Id("m");
        Formula jointReadout = Call("jointObservation", readout);
        Formula finiteRelation = Call(
            "finiteHorizonKernel", update, jointReadout, depth);
        Formula completeRelation = Call(
            "ker", Call("completeItinerary", update, jointReadout));

        Formula outputFamily = Seq(
            Open, F.Id("i"), Colon, Sp, interfaces, Close, Sp, To, Sp, F.Id("Type"));
        Formula readoutFamily = Seq(
            Open, F.Id("i"), Colon, Sp, interfaces, Close, Sp, To, Sp,
            states, Sp, To, Sp, outputs);

        return Disp(Seq(
            Forall, Sp,
            Typed(states, F.Id("Type")), Comma, Sp,
            Typed(interfaces, F.Id("Type")), Comma, Sp,
            Typed(F.Id("O"), outputFamily), Comma, RowBreak, Grp(),
            Typeclass("Finite", states), Comma, Sp,
            Typed(update, new Formula.TypeArrow(states, states)), Comma, Sp,
            Typed(readout, readoutFamily), Comma, RowBreak, Grp(),
            Exists, Sp, depth, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            finiteRelation, Sp, Eq, Sp, completeRelation, Dot));
    }
}

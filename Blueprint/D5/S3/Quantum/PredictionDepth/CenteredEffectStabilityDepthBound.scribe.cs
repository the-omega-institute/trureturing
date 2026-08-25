using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class CenteredEffectStabilityDepthBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite centered-effect tower reaches its terminal predictive space within its dimension gap.",
        H("Finite Stability Depth of the Centered-Effect Tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("centered-effect-stability-depth-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/CenteredEffectStabilityDepthBound."
                        + "centered_effect_stability_depth_bound"),
                H("The first stable depth is bounded by visible dimension growth"),
                StatementSource.FromAuthor(StabilityDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the imported real HermitianTraceZero(d) space. The finite "
                            + "stage towerSpace(H,E,m) is generated recursively from the centered "
                            + "effects, while predictiveSpace(H,E) is the real span of all finite "
                            + "Heisenberg iterates.")),
                    Paragraph(Text(
                        "The public stabilityDepth(H,E) is the infimum of the natural indices m "
                            + "for which towerSpace(H,E,m) equals towerSpace(H,E,m+1). Finite "
                            + "dimension makes this test nonempty, and one-step stability is "
                            + "permanent by the imported tower theorem.")),
                    Paragraph(Text(
                        "Every strict stage inclusion raises real finrank by at least one. Thus the "
                            + "least stable index is at most the terminal finrank gain. The exact "
                            + "trace-zero Hermitian dimension d squared minus one gives the second "
                            + "bound on the same source carrier.")),
                    Paragraph(Text(
                        "The final two displayed clauses identify predictiveSpace(H,E) first with "
                            + "the supremum of all finite tower stages and then identify that "
                            + "supremum with the stage at stabilityDepth(H,E). Repository and "
                            + "pinned-library searches found no theorem packaging these four "
                            + "clauses; the proof applies the existing carrier, tower, predictive "
                            + "space, finrank, and natural-infimum declarations directly."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula StabilityDepthFormula()
    {
        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrier = Call("HermitianTraceZero", d);
        Formula heisenberg = F.Id("H");
        Formula effects = F.Id("E");
        Formula depth = Call("stabilityDepth", heisenberg, effects);
        Formula initial = Call("towerSpace", heisenberg, effects, D(0));
        Formula terminal = Call("predictiveSpace", heisenberg, effects);
        Formula stageUnion = Call("iSupTowerSpace", heisenberg, effects);
        Formula stableStage = Call("towerSpace", heisenberg, effects, depth);
        Formula initialRank = Call("finrank", real, initial);
        Formula terminalRank = Call("finrank", real, terminal);
        Formula terminalGap = Seq(terminalRank, Sp, Minus, Sp, initialRank);
        Formula ambientGap = Seq(
            d, Caret, Grp(D(2)), Sp, Minus, Sp, D(1), Sp, Minus, Sp, initialRank);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Comma, Sp, r, Colon, Sp,
            Operatorname, Grp(F.Id("Nat")), Comma, Sp,
            d, Sp, Geq, Sp, D(1), Comma, RowBreak, Grp(),
            heisenberg, Colon, Sp, Call("LinearMap", real, carrier, carrier), Comma, Sp,
            effects, Colon, Sp, Call("Fin", Seq(r, Plus, D(1))), Sp, To, carrier,
            Comma, RowBreak, Grp(),
            depth, Sp, Leq, Sp, terminalGap, Sp, Land, RowBreak, Grp(),
            terminalGap, Sp, Leq, Sp, ambientGap, Sp, Land, RowBreak, Grp(),
            terminal, Sp, Eq, Sp, stageUnion, Sp, Land, RowBreak, Grp(),
            stageUnion, Sp, Eq, Sp, stableStage, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

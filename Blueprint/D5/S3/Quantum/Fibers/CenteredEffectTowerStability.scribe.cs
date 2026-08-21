using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class CenteredEffectTowerStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-step stability of a centered-effect Heisenberg tower is permanent.",
        H("Permanent Stability of the Centered-Effect Tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("heisenberg-tower-one-step-stability-is-permanent"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/CenteredEffectTowerStability."
                        + "heisenberg_tower_once_stable_permanently"),
                H("One-step Heisenberg tower stability is permanent"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the real HermitianTraceZero(d) subspace imported from "
                            + "the readout-fiber family. The effect family is the source's finite "
                            + "centered effect family and the real-linear map is its Heisenberg "
                            + "dual action on that carrier.")),
                    Paragraph(Text(
                        "The visible stage V_n is constructed recursively from the initial real "
                            + "span and the image of the preceding stage under the Heisenberg map. "
                            + "The residual stage R_n is V_n orthogonal complement.")),
                    Paragraph(Text(
                        "If V_m equals V_(m+1), the recursion has no new image at stage m. "
                            + "Induction gives equality of every later visible stage, and applying "
                            + "orthogonal-complement congruence gives the matching residual equality."))),
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

    private static Formula Stage(string name, Formula map, Formula effects, Formula index) =>
        Call(name, map, effects, index);

    private static Formula StabilityFormula()
    {
        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula m = F.Id("m");
        Formula s = F.Id("s");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrier = Call("HermitianTraceZero", d);
        Formula map = F.Id("H");
        Formula effects = F.Id("E");
        Formula stageM = Stage("towerSpace", map, effects, m);
        Formula stageM1 = Stage("towerSpace", map, effects, Seq(m, Plus, D(1)));
        Formula stageLater = Stage("towerSpace", map, effects, Seq(m, Plus, s));
        Formula residualM = Stage("residualSpace", map, effects, m);
        Formula residualLater = Stage("residualSpace", map, effects, Seq(m, Plus, s));

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, r, Comma, Sp, m, Colon, Sp,
            Operatorname, Grp(F.Id("Nat")), Comma, RowBreak, Grp(),
            map, Colon, Sp, Call("LinearMap", real, carrier, carrier), Comma, Sp,
            effects, Colon, Sp, Operatorname, Grp(F.Id("Fin")), Open,
            r, Plus, D(1), Close, Sp, To, carrier, Comma, RowBreak, Grp(),
            stageM, Sp, Eq, Sp, stageM1, Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Open, Forall, Sp, s, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            stageLater, Sp, Eq, Sp, stageM, Close, Sp, Land, RowBreak, Grp(),
            Open,
            Open, Forall, Sp, s, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            residualLater, Sp, Eq, Sp, residualM, Close,
            Close, Dot));
    }
}

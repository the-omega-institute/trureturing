using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class KnasterTarskiWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Dynamics/KnasterTarskiWitness",
                "Frozen proofs assemble the extremal fixed-point theorem with its three-state instance."),
            H("Knaster–Tarski Witness"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("knaster-tarski-with-three-cycle-instance"),
                    H("Extremal fixed points with the three-state successor instance"),
                    LeanTheorem(
                        "D5/S1/Dynamics/KnasterTarskiWitness.knaster_tarski_with_three_cycle_instance"),
                    Disp(Seq(Open, Forall, Sp, F.Id("f"), Colon, Alpha, To, Underscore, Grp(F.Id("o")), Alpha, Comma, Esc, Operatorname, Grp(F.Id("lfp")), Open, F.Id("f"), Close, Eq, Min, Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Esc, Land, Esc, Operatorname, Grp(F.Id("gfp")), Open, F.Id("f"), Close, Eq, Max, Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Close, Esc, Land, Esc, Operatorname, Grp(F.Id("lfp")), Open, SigmaLower, Underscore, Grp(D(3)), Close, Eq, Varnothing, Esc, Land, Esc, Operatorname, Grp(F.Id("gfp")), Open, SigmaLower, Underscore, Grp(D(3)), Close, Eq, Mathrm, Grp(F.Id("univ")), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "For every monotone endomorphism of a complete lattice, the least "
                            + "fixed point is the least element of the fixed-point set and the "
                            + "greatest fixed point is its greatest element. For the three-state "
                            + "successor-cycle operator, the least fixed point is the empty set "
                            + "and the greatest fixed point is the full state set.")),
                        Paragraph(Text(
                            "The statement is assembly-only: both conjuncts are witnessed by "
                            + "their frozen proofs in the Knaster–Tarski module, so the "
                            + "theorem packages the general result and its concrete instance "
                            + "behind a single declaration without re-proving either.")))
                ))));
}

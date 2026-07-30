using static StrataLint.Scribe.DefinitionDsl;

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
                new DocumentBlock.Describe(
                    DescribeId.Create("knaster-tarski-with-three-cycle-instance"),
                    DescribeKind.Theorem,
                    H("Extremal fixed points with the three-state successor instance"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Dynamics/KnasterTarskiWitness.knaster_tarski_with_three_cycle_instance")),
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
                            + "behind a single declaration without re-proving either."))),
                    LatexStatement.Create(
                        @"$$(\forall f\colon\alpha\to_{o}\alpha,\ "
                        + @"\operatorname{lfp}(f)=\min\operatorname{Fix}(f)\ \land\ "
                        + @"\operatorname{gfp}(f)=\max\operatorname{Fix}(f))\ \land\ "
                        + @"\operatorname{lfp}(\sigma_{3})=\varnothing\ \land\ "
                        + @"\operatorname{gfp}(\sigma_{3})=\mathrm{univ}.$$")))));
}

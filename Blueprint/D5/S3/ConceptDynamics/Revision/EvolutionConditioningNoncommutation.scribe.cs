using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Revision;

internal sealed class EvolutionConditioningNoncommutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evolution and conditioning can fail to commute, but invariant evidence restores it.",
        H("Evolution and Conditioning Noncommutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("evolution-and-conditioning-do-not-commute"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation."
                        + "evolution_and_conditioning_do_not_commute"),
                H("Evolution and conditioning need not commute"),
                StatementSource.FromAuthor(NoncommutationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is no general commutation law for conditioning and arbitrary set "
                            + "evolution: some carrier, set transformer, evidence set, and admitted-"
                            + "state set make condition-then-evolve differ from evolve-then-condition.")),
                    Paragraph(Text(
                        "On the Boolean carrier, the saturating evolution sends a nonempty set to "
                            + "the entire carrier and the empty set to the empty set. With admitted "
                            + "states {false} and evidence {true}, conditioning first produces the "
                            + "empty set, whereas evolving first and then conditioning produces "
                            + "{true}."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("image-evolution-commutes-with-conditioning"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation."
                        + "image_evolution_commutes_with_conditioning"),
                H("Invariant evidence restores commutation for image evolution"),
                StatementSource.FromAuthor(InvariantCommutationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any pointwise transition, if pulling the evidence set back along the "
                            + "transition returns the same evidence set, then direct-image evolution "
                            + "commutes with conditioning for every admitted-state set.")),
                    Paragraph(Text(
                        "The invariance condition rewrites the evidence set as a preimage. The "
                            + "direct image of the resulting intersection is exactly the intersection "
                            + "of the evolved states with the evidence set, with no injectivity "
                            + "assumption on the transition."))),
                DescribeRole.Theorem))));

    private static Formula NoncommutationFormula()
    {
        Formula carrier = F.Id("X");
        Formula evolution = F.Id("F");
        Formula evidence = F.Id("P");
        Formula states = F.Id("A");
        Formula setOfCarrier = Call("Set", carrier);
        Formula conditionFirst = Call("F", Call("conditioning", evidence, states));
        Formula evolveFirst = Call("conditioning", evidence, Call("F", states));

        return Disp(Seq(
            Exists, Sp, carrier, Colon, Sp, F.Id("Type"), Comma, Sp,
            evolution, Colon, Sp, setOfCarrier, Sp, To, Sp, setOfCarrier, Comma, Sp,
            evidence, Comma, Sp, states, Colon, Sp, setOfCarrier, Comma, Esc,
            conditionFirst, Sp, Neq, Sp, evolveFirst, Dot));
    }

    private static Formula InvariantCommutationFormula()
    {
        Formula carrier = F.Id("X");
        Formula transition = F.Id("f");
        Formula evidence = F.Id("P");
        Formula states = F.Id("A");
        Formula setOfCarrier = Call("Set", carrier);
        Formula invariantEvidence = Equal(Call("preimage", transition, evidence), evidence);
        Formula conditionFirst = Call(
            "imageEvolution",
            transition,
            Call("conditioning", evidence, states));
        Formula evolveFirst = Call(
            "conditioning",
            evidence,
            Call("imageEvolution", transition, states));

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, F.Id("Type"), Comma, Sp,
            transition, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Sp,
            evidence, Comma, Sp, states, Colon, Sp, setOfCarrier, Comma, Esc,
            invariantEvidence, Sp, Rightarrow, Sp,
            conditionFirst, Sp, Eq, Sp, evolveFirst, Dot));
    }
}

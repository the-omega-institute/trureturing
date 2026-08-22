using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class TargetKnowledgeWithoutWorldKnowledgeDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/TargetKnowledgeWithoutWorldKnowledge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target-sufficient concept need not determine the complete world state.",
        H("Target Knowledge Without World Knowledge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-first-coordinate-is-sufficient-but-incomplete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "answer_concept_sufficient_but_incomplete"),
                H("The first coordinate is sufficient but incomplete"),
                StatementSource.FromAuthor(ConcreteWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a world to be a pair of Boolean coordinates. The target and the "
                            + "answer concept both read the first coordinate, so the canonical "
                            + "target-image readout factors through that concept.")),
                    Paragraph(Text(
                        "The concept is not equivalent to complete world knowledge. It identifies "
                            + "the worlds (false, false) and (false, true), while the identity "
                            + "readout distinguishes them, so no reverse factor can recover the "
                            + "second coordinate."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("target-knowledge-does-not-require-world-knowledge"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "target_knowledge_without_world_knowledge"),
                H("Target knowledge does not require world knowledge"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exist a state space, a target readout, and a concept from which the "
                            + "canonical target answer can be recovered even though the concept is "
                            + "not equivalent to the identity readout on states.")),
                    Paragraph(Text(
                        "The Boolean-pair construction supplies the witness: retain the first bit "
                            + "needed by the target and discard the independent second bit. Thus "
                            + "target sufficiency is strictly weaker than complete world "
                            + "recovery."))),
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

    private static Formula Named(Formula id) =>
        Seq(Operatorname, Grp(id));

    private static Formula ConcreteWitnessFormula()
    {
        Formula boolType = Named(F.Id("Bool"));
        Formula state = F.Id("X");
        Formula target = F.Id("T");
        Formula concept = F.Id("C");
        Formula world = F.Id("W");
        Formula first = Named(F.Id("fst"));
        Formula identity = Named(F.Id("id"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            state, Sp, Eq, Sp, boolType, Sp, Times, Sp, boolType, Comma, RowBreak, Grp(),
            target, Sp, Eq, Sp, concept, Sp, Eq, Sp, first, Comma, Sp,
            world, Sp, Eq, Sp, identity, Comma, RowBreak, Grp(),
            Call("Refines", Call("canonicalTargetReadout", target), concept),
            Sp, Land, Sp, Neg, Sp, Call("ConceptEquivalent", concept, world), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ExistenceFormula()
    {
        Formula state = F.Id("X");
        Formula targetType = F.Id("Target");
        Formula coordinateType = F.Id("Coordinate");
        Formula target = F.Id("T");
        Formula concept = F.Id("C");
        Formula type = Named(F.Id("Type"));
        Formula identity = new Formula.Subscript(F.Id("id"), state);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp, state, Comma, Sp, targetType, Comma, Sp, coordinateType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            target, Colon, Sp, state, Sp, To, Sp, targetType, Comma, Sp,
            concept, Colon, Sp, state, Sp, To, Sp, coordinateType, Comma, RowBreak, Grp(),
            Call("Refines", Call("canonicalTargetReadout", target), concept),
            Sp, Land, Sp, Neg, Sp, Call("ConceptEquivalent", concept, identity), Dot,
            End, Grp(F.Id("gathered"))));
    }
}

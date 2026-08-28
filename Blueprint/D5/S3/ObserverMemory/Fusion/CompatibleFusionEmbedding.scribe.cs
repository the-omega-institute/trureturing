using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class CompatibleFusionEmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An intersection completion is exactly the compatible image of its component completions.",
        H("Compatible Fusion Embedding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("intersection-completion-embeds-as-the-compatible-image"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Fusion/CompatibleFusionEmbedding."
                        + "compatible_fusion_embedding"),
                H("The intersection completion embeds as the compatible image"),
                StatementSource.FromAuthor(EmbeddingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let qi be a family of readouts on a state type Y with update u. Each "
                            + "readout defines complete-future equivalence through the repository's "
                            + "complete itinerary. The fused completion is the quotient by the "
                            + "intersection of these component relations, and J sends a fused class "
                            + "to its class in every component quotient.")),
                    Paragraph(Text(
                        "The compatible subset Comp consists exactly of component tuples z for "
                            + "which there is one state y whose canonical class in every component "
                            + "is zi. The theorem proves that J is injective, its range is Comp, and "
                            + "the fused quotient is canonically equivalent to Comp with underlying "
                            + "map J.")),
                    Paragraph(Text(
                        "Advancing both states shifts equality of complete itineraries and therefore "
                            + "preserves every component relation. The induced fused and component "
                            + "updates require no additional hypothesis, and the theorem proves that "
                            + "J intertwines all of them.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Quotient.map and Quotient.exact for the quotient "
                            + "arguments, followed by Equiv.ofInjective and Equiv.setCongr for the "
                            + "canonical equivalence. Repository search found related two-component "
                            + "refinement and product-fullness results, but no declaration containing "
                            + "all four family-indexed conclusions."))),
                DescribeRole.Theorem))));

    private static Formula EmbeddingFormula()
    {
        Formula update = F.Id("u");
        Formula readout = F.Id("q");
        Formula embedding = F.Id("J");
        Formula embeddingDefiniens = Call(
            "completionEmbedding", Call("componentCompletionRelation", update, readout));
        Formula fused = Call("Fused", readout);
        Formula compatible = Call("Comp", readout);
        Formula state = F.Id("z");
        Formula component = F.Id("i");
        Formula equivalence = F.Id("e");
        Formula advancedEmbeddingAtComponent = Seq(
            Call("J", Call("completedFusionDynamics", update, readout, state)),
            Underscore, Grp(component));
        Formula embeddingAtComponent = Seq(
            Call("J", state), Underscore, Grp(component));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("I"), Comma, Sp, F.Id("Y"), Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            F.Id("O"), Colon, Sp, F.Id("I"), Sp, To, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak,
            update, Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"), Comma, Sp,
            readout, Colon, Sp, Prod, Underscore, Grp(F.Id("i")), Sp,
            Open, F.Id("Y"), Sp, To, Sp,
            F.Id("O"), Underscore, Grp(F.Id("i")), Close, Comma, RowBreak,
            Operatorname, Grp(F.Id("let")), Sp, embedding, Sp, Colon, Eq, Sp,
            embeddingDefiniens, Semi, RowBreak,
            Call("Injective", embedding), Sp, Land, RowBreak,
            Open, Forall, Sp, state, InMacro, Sp, fused, Comma, Sp,
            Forall, Sp, component, InMacro, Sp, F.Id("I"), Comma, RowBreak,
            advancedEmbeddingAtComponent, Sp, Eq, Sp,
            Call("completedComponentDynamics", update, readout, component,
                embeddingAtComponent),
            Close, Sp, Land, RowBreak,
            Call("range", embedding), Sp, Eq, Sp, compatible, Sp, Land, RowBreak,
            Exists, Sp, equivalence, Colon, Sp, fused, Sp, Equiv, Sp, compatible,
            Comma, Sp, Forall, Sp, state, InMacro, Sp, fused, Comma, Sp,
            Call("coe", Call("e", state)), Sp, Eq, Sp,
            Call("J", state), Dot,
            End, Grp(F.Id("gathered"))));
    }
}

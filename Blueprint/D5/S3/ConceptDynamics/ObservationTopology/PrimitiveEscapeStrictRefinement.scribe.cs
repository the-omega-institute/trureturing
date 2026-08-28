using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class PrimitiveEscapeStrictRefinementDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive escape is exactly strict refinement of family observation topology.",
        H("Primitive Escape as Strict Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("primitive-escape-is-strict-observation-refinement"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/ObservationTopology/"
                    + "PrimitiveEscapeStrictRefinement."
                    + "primitiveEscape_iff_strict_topology_refinement"),
            H("Primitive escape is exactly strict observation refinement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The old family readout records every definition in Gamma. The extended "
                        + "readout pairs those coordinates with the candidate value.")),
                Paragraph(Text(
                    "Every old observation-open set remains open after extension because the "
                        + "old readout is the first projection of the extended readout.")),
                Paragraph(Text(
                    "A primitive escape separates two states on which all old definitions "
                        + "agree, producing an open candidate fiber unavailable to the old "
                        + "topology. Conversely, failure of primitive escape makes the "
                        + "candidate fiber-constant and leaves both topologies equal.")),
                Paragraph(Text(
                    "The biconditional is asserted only under the displayed inhabited-state "
                        + "hypothesis."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula inputOutput = F.Id("InputOutput");
        Formula output = F.Id("Output");
        Formula family = F.Id("Gamma");
        Formula candidate = F.Id("candidate");
        Formula oldTopology = Call(
            "partitionTopology",
            Call("familyReadout", family));
        Formula extendedTopology = Call(
            "partitionTopology",
            Call("extendedFamilyReadout", family, candidate));
        Formula conclusion = Seq(
            Call("PrimitiveEscape", family, candidate), Sp, Iff, Sp,
            Call("StrictObservationRefinement", oldTopology, extendedTopology));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, family, Colon, Sp,
            Call("Set", Call("Concept", state, inputOutput)), Comma, Sp,
            candidate, Colon, Sp, Call("Concept", state, output), Comma,
            RowBreak, Grp(),
            Call("Nonempty", state), Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

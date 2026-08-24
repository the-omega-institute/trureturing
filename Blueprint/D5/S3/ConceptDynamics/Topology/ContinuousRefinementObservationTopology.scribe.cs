using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class ContinuousRefinementObservationTopologyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Topology/ContinuousRefinementObservationTopology."
            + "continuous_refinement_observation_topology";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous refinement factorization makes every coarse observation-open set "
            + "open for the refined readout.",
        H("Continuous Refinement Observation Topology"),
        Blocks(Describe.Lean(
            DescribeId.Create("continuous-refinement-observation-topology"),
            DeclarationHandle.Create(Declaration),
            H("Continuous refinement makes the observation topology finer"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation topology of a readout is constructed directly as the "
                        + "topology induced from its value space. No separate observation-"
                        + "topology definition is introduced.")),
                Paragraph(Text(
                    "Let the coarse readout factor as a continuous projection after the refined "
                        + "readout. Every subset open for the coarse induced topology is then "
                        + "open for the refined induced topology.")),
                Paragraph(Text(
                    "The proof applies the pinned library laws Continuous.le_induced, "
                        + "induced_mono, and induced_compose directly."))),
            DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coarseValue = F.Id("B");
        Formula refinedValue = F.Id("R");
        Formula coarse = F.Id("C");
        Formula refined = F.Id("D");
        Formula projection = F.Id("p");
        Formula states = F.Id("U");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula factorization = Seq(
            coarse, Sp, Eq, Sp, projection, Sp, Circ, Sp, refined);
        Formula projectionContinuous = Call("Continuous", projection);
        Formula coarseTopology = Call(
            "induced", coarse, Call("topology", coarseValue));
        Formula refinedTopology = Call(
            "induced", refined, Call("topology", refinedValue));
        Formula openInCoarse = Call("IsOpen", coarseTopology, states);
        Formula openInRefined = Call("IsOpen", refinedTopology, states);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coarseValue, Comma, Sp, refinedValue,
            Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Typeclass("TopologicalSpace", coarseValue), Comma, Sp,
            Typeclass("TopologicalSpace", refinedValue), Comma,
            RowBreak, Grp(),
            coarse, Colon, Sp, Arrow(state, coarseValue), Comma, Sp,
            refined, Colon, Sp, Arrow(state, refinedValue), Comma, Sp,
            projection, Colon, Sp, Arrow(refinedValue, coarseValue), Comma,
            RowBreak, Grp(),
            Open, factorization, Sp, Land, Sp, projectionContinuous, Close,
            Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, states, Colon, Sp, Call("Set", state), Comma, Sp,
            openInCoarse, Sp, Rightarrow, Sp, openInRefined, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

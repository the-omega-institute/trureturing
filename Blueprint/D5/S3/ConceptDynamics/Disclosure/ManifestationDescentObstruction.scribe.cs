using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Disclosure;

internal sealed class ManifestationDescentObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Disclosure/ManifestationDescentObstruction."
            + "manifestation_excludes_noninterference_descent";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A distinction that becomes publicly visible after evolution cannot descend through "
            + "a current public readout that identifies the two states.",
        H("Manifestation Descent Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("manifestation-excludes-noninterference-descent"),
            DeclarationHandle.Create(Declaration),
            H("Manifestation obstructs noninterference descent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The future public readout is constructed by composing the evolution "
                        + "with the output interface. A descent through the current readout "
                        + "would preserve equality on every current-readout fiber.")),
                Paragraph(Text(
                    "The selected states occupy one such fiber but have different future "
                        + "outputs. Their manifestation therefore directly contradicts every "
                        + "candidate descent map."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula currentType = F.Id("L");
        Formula futureState = F.Id("Y");
        Formula futureType = F.Id("B");
        Formula low = F.Id("l");
        Formula flow = F.Id("F");
        Formula output = F.Id("O");
        Formula stateAA = F.Id("xAA");
        Formula stateAB = F.Id("xAB");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula futureReadout = Seq(output, Sp, Circ, Sp, flow);
        Formula PublicAfter(Formula value) => Apply(output, Apply(flow, value));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, currentType, Comma, Sp,
                futureState, Comma, Sp, futureType, Colon, Sp, type, Comma),
            Seq(
                low, Colon, Sp, state, Sp, To, Sp, currentType, Comma, Sp,
                flow, Colon, Sp, state, Sp, To, Sp, futureState, Comma),
            Seq(
                output, Colon, Sp, futureState, Sp, To, Sp, futureType,
                Comma, Sp, stateAA, Comma, Sp, stateAB, Colon, Sp, state, Comma),
            Seq(
                Apply(low, stateAA), Sp, Eq, Sp, Apply(low, stateAB), Sp, Land, Sp,
                PublicAfter(stateAA), Sp, Neq, Sp, PublicAfter(stateAB),
                Sp, Rightarrow),
            Seq(
                Neg, Sp, Call("Refines", futureReadout, low), Dot),
        ]));
    }
}

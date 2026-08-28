using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class ConsumptionProductionInputSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Governance/ConsumptionProductionInputSeparation."
            + "consumption_not_inverse_to_production_input";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite two-artifact model separates runtime consumption from production input.",
        H("Consumption and Production Input Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("consumption-not-inverse-to-production-input"),
                DeclarationHandle.Create(Declaration),
                H("Consumption is not inverse to production input"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take Bool as the two-element artifact type, with x=false and y=true. "
                            + "The runtime-consumer set at x is the singleton containing y.")),
                    Paragraph(Text(
                        "The partial production-input map is defined at y with the empty set. "
                            + "Thus y consumes x at runtime while x is absent from the inputs "
                            + "used to produce y.")),
                    Paragraph(Text(
                        "The witness keeps the two relations distinct: runtime reads need not "
                            + "be inverse images of production-input records."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula artifact = F.Id("Bool");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula consumers = F.Id("consumers");
        Formula prodInputs = F.Id("prodInputs");
        Formula setArtifact = Call("Set", artifact);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp, x, Comma, Sp, y, Colon, Sp, artifact, Comma,
            RowBreak, Grp(),
            consumers, Colon, Sp, Arrow(artifact, setArtifact), Comma, Sp,
            prodInputs, Colon, Sp, Arrow(artifact, Call("Option", setArtifact)), Comma,
            RowBreak, Grp(),
            x, Sp, Neq, Sp, y, Sp, Land, Sp,
            Apply(consumers, x), Sp, Eq, Sp, OpenBrace, y, CloseBrace, Sp, Land,
            RowBreak, Grp(),
            y, Sp, InMacro, Sp, Apply(consumers, x), Sp, Land, Sp,
            Apply(prodInputs, y), Sp, Eq, Sp, Call("some", Emptyset), Sp, Land,
            RowBreak, Grp(),
            Neg, Sp, Open, x, Sp, InMacro, Sp, Emptyset, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

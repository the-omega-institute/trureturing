using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class EndStateOmitsPreemptingCauseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered preemption is expressed through endpoint, cause, admission, and anchor primitives.",
        H("End State Omits Preempting Cause Arena"),
        Blocks(Describe.Lean(
            DescribeId.Create("end-state-preemption-arena"),
            DeclarationHandle.Create(Prefix + "endStateOmitsPreemptingCauseArena"),
            H("Preemption trace arena"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("endStateOmitsPreemptingCauseArena"),
                Colon, Sp, F.Id("PrimitiveLawArena"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Two CUTs and two coded ADMITS are evaluated at the named trace anchors, including the endpoint-factorization obstruction."))),
            DescribeRole.Definition))));
}

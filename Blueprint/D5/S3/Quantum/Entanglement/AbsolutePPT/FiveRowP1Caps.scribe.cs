using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class FiveRowP1CapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tail-derived upper caps for the five-row scalar system.",
        H("FiveRowP1Caps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiverowp1caps-chordok"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Caps.chordOK"),
                H("Rational lower chord endpoint guards"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The square-tail branch uses a rational chord whose endpoint values are nonnegative and whose squares lie below q. The linear-tail branch uses the upper endpoint of D. The cases H=0 and an upper D endpoint of zero are retained without dividing by zero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiverowp1caps-cap-sound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Caps.cap_sound"),
                H("Ninth cap from the original tail disjunction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The square-tail branch uses a rational chord whose endpoint values are nonnegative and whose squares lie below q. The linear-tail branch uses the upper endpoint of D. The cases H=0 and an upper D endpoint of zero are retained without dividing by zero."))), DescribeRole.Theorem))));
}

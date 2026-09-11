using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class HFEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed small copy of the hereditarily finite set universe supports literal event codes.",
        H("Hereditary Finite Event Codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("small-hf-universe-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/HFEncoding.hf_equiv"),
                H("The exact set universe"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Event names inhabit a fixed small copy of the elements of Mathlib's von Neumann omega stage. "
                    + "The explicit equivalence retains the set representation. Natural codes are finite ordinals "
                    + "and ordered pairs are literal Kuratowski pairs; pair injectivity applies Mathlib's theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-event-set-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/HFEncoding.finite_set_equiv"),
                H("Finite event sets and HF sets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every HF set has finitely many members. Encoding a finite set and enumerating those members "
                    + "are mutual inverses, with no common bound on archive size. This is a Lean representation "
                    + "theorem over Mathlib's set universe; it makes no first-order ZFC conservativity claim."))),
                DescribeRole.Definition))));
}

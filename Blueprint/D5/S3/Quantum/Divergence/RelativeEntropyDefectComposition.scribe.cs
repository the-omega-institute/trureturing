using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class RelativeEntropyDefectCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative-entropy loss telescopes exactly along two composable state channels.",
        H("Relative-Entropy Defect Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative-entropy-defect-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/RelativeEntropyDefectComposition."
                        + "relative_entropy_defect_composition"),
                H("Relative-entropy defects form an additive channel chain"),
                StatementSource.FromAuthor(Disp(Seq(
                    DeltaLower, Underscore, Grp(Psi, Circ, Phi),
                    Open, Rho, Comma, Sp, SigmaLower, Close, Sp, Eq, Sp,
                    DeltaLower, Underscore, Grp(Phi),
                    Open, Rho, Comma, Sp, SigmaLower, Close, Sp, Plus, Sp,
                    DeltaLower, Underscore, Grp(Psi), Open,
                    Phi, Rho, Comma, Sp, Phi, SigmaLower, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each state channel, its defect is the source relative entropy "
                            + "minus the target relative entropy after applying the channel.")),
                    Paragraph(Text(
                        "Expanding the three defects makes the intermediate relative entropy "
                            + "cancel, leaving the exact composition identity."))),
                DescribeRole.Theorem))));
}

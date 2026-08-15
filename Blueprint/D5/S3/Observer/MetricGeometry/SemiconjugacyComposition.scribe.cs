using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class SemiconjugacyCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Lipschitz post-map bounds composite defect by its two component defects.",
        H("Semiconjugacy Defect Under Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("semiconjugacy-defect-is-subadditive-under-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/SemiconjugacyComposition."
                        + "semiconjugacy_defect_composition"),
                H("Semiconjugacy defect is subadditive under composition"),
                StatementSource.FromAuthor(Disp(Seq(
                    DeltaLower, Open, Rho, Circ, Pi, Semi, Sp, Tau, Comma, Sp, Omega, Close,
                    Sp, Leq, Sp,
                    F.Id("K"), Sp,
                    DeltaLower, Open, Pi, Semi, Sp, Tau, Comma, Sp, SigmaLower, Close,
                    Sp, Plus, Sp,
                    DeltaLower, Open, Rho, Semi, Sp, SigmaLower, Comma, Sp, Omega, Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Define each defect as the supremum of the extended distance between "
                        + "projecting after the source update and applying the target update "
                        + "after projection. For a K-Lipschitz post-map, insert the intermediate "
                        + "updated projection. The triangle inequality splits the resulting "
                        + "distance, the Lipschitz estimate bounds the first term, and each "
                        + "pointwise term is bounded by its defining supremum."))),
                DescribeRole.Theorem))));
}

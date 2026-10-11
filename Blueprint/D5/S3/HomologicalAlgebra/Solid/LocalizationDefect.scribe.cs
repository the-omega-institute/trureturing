using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class LocalizationDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact unbounded locality test for the protected solidification reflector. This constructs the actual two-term defect, not a replacement hypothesis. Its vanishing detects solid homology in every integer degree. A universal local replacement and its comparison with `DerivedCategory Solid` remain separate mathematical obligations.",
        H("Localization Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-localizationdefect-iszero-solidcomplexdefect-iff"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/LocalizationDefect.isZero_solidComplexDefect_iff"),
                H("is Zero solid Complex Defect iff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defect vanishes in the derived category precisely for complexes whose homology is solid; no bound on degrees is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-localizationdefect-isiso-solidderivedendomorphism-q-iff"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/LocalizationDefect.isIso_solidDerivedEndomorphism_Q_iff"),
                H("is Iso solid Derived Endomorphism Q iff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derived natural transformation on the localization of any complex has the same exact all-degree locality criterion."))),
                DescribeRole.Theorem))));
}

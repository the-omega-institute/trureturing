using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class DualNumberResidueExtensionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/HomologicalAlgebra/DualNumberResidueExtension.";

    private static readonly LibraryNoteRef StacksSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/stacksproject2026dualnumberext");

    private static readonly LibraryNoteRef WeibelSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/weibel1994torext");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The epsilon-ideal sequence over the rational dual numbers is a short exact "
            + "sequence with nonzero degree-one extension class.",
        H("A Nonzero Dual-Number Residue Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dual-number-residue-complex"),
                DeclarationHandle.Create(Prefix + "dualNumberResidueComplex"),
                H("The epsilon-ideal residue complex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(StacksSource, WeibelSource),
                Blocks(Paragraph(Text(
                    "Let A be the rational dual-number ring and let the residue copy of "
                        + "the rationals carry its A-module structure through augmentation. "
                        + "The complex sends q to q epsilon and then takes augmentation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dual-number-residue-extension-nonzero"),
                DeclarationHandle.Create(Prefix + "dual_number_residue_extension_nonzero"),
                H("The residue extension class is nonzero"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(StacksSource, WeibelSource),
                Blocks(
                    Paragraph(Text(
                        "The two coordinate maps make the displayed complex short exact. "
                            + "If its Ext-one class vanished, Mathlib's contravariant long "
                            + "exact sequence and the Ext-zero/Hom equivalence would give a "
                            + "retraction of the epsilon inclusion.")),
                    Paragraph(Text(
                        "Evaluating the retraction at epsilon gives one. A-linearity gives "
                            + "zero because epsilon acts through augmentation on the residue "
                            + "module. This contradiction proves that the extension class is "
                            + "nonzero.")),
                    Paragraph(Text(
                        "The sources support the periodic dual-number resolution and the "
                            + "standard Ext machinery. The concrete rational specialization "
                            + "and nonvanishing argument are repository-derived. The next "
                            + "frontier is to identify the full graded Ext algebra and its "
                            + "Yoneda product."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula() => F.Disp(F.Seq(
        F.Exists, F.Sp, F.Id("hS"), F.Colon, F.Sp,
        F.Id("ShortExact"), F.Open, F.Id("Sepsilon"), F.Close, F.Comma, F.Sp,
        F.Id("hS"), F.Dot, F.Id("extClass"),
        F.Sp, F.Neq, F.Sp, F.D(0), F.Sp, F.InMacro, F.Sp,
        F.Id("Ext"), F.Caret, F.Grp(F.D(1)), F.Underscore, F.Grp(F.Id("A")),
        F.Open, F.Mathbb, F.Grp(F.Id("Q")), F.Comma, F.Sp,
        F.Mathbb, F.Grp(F.Id("Q")), F.Close));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.BoxCover;

internal sealed class CheckedRationalBoxCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An executable rational forest supplies locally justified proofs for a continuous residual-sublevel cover.",
        H("Checked Rational Box Covers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("checked-rational-box-cover-step"),
                DeclarationHandle.Create("D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.Step"),
                H("Typed cover, exclusion and split instructions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Instruction indices are finite, but the covered input space consists of real vectors. A split records two children. Unsupported contractor instructions are not silently accepted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("checked-rational-box-cover-check-forest"),
                DeclarationHandle.Create("D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checkForest"),
                H("Check all arithmetic, expression identities and closed split inclusions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The check recomputes rational expression bounds, compares residual syntax after removing endpoint annotations, and verifies strict child order and inclusion of both closed halves. It does not consume an external success report."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("checked-rational-box-cover-covers-sublevel"),
                DeclarationHandle.Create("D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checked_forest_covers_sublevel"),
                H("An accepted forest covers every real sublevel point in a root box"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("RationalIntervalExpression supplies each numerical real enclosure. Expression erasure binds it to the specified residual, and exact endpoint comparisons retain both split halves. These results construct the actual LocalStep proof terms consumed by FiniteSublevelCover.")),
                    Paragraph(Text("The theorem supplies no Krawczyk contraction adapter and makes no claim about the full MUB phase-domain instance. Each physical application must still identify the expression semantics with its actual residual. Kernel acceptance requires compiling the source and the concrete data checks."))),
                DescribeRole.Theorem))));
}

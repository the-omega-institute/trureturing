using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class UnitAcceptanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acceptance of the rounded unit producer.",
        H("Acceptance of the rounded unit producer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitacceptance-check-unitpolynomialpayload"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.check_unitPolynomialPayload"),
                H("Every actual source cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive natural radius R, rational shift s, any mesh depth d and scalar precision m, the rounded payload for each actual source cell passes the canonical checker at Taylor depth 4m+4. Both polynomial components are the constant one.")),
                    Paragraph(Text("Cutoff endpoints are rounded outwards to multiples of 2^-32. The signed differences and squares retain checker acceptance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitacceptance-unitpolynomialpayloads-cells-accepted"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance.unitPolynomialPayloads_cells_accepted"),
                H("List and cell alignment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Mapping this producer over sourceCells gives exactly one payload per adjacent source pair. The mapped list has the required first and last hull endpoints, each index retrieves its actual cell payload, and every cell check in the full Boolean conjunction succeeds."))),
                DescribeRole.Theorem)),
        []));
}

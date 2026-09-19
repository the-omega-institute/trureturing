using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Generic;

internal sealed class CellCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic rational cell construction.",
        H("Generic rational cell construction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("generic-cellcertificate-cell-certificate"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Generic/CellCertificate.cell_certificate"),
                H("Acceptance and shrinking width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive natural R, rational shift s, mesh depth d, scalar precision m, actual canonical cell [a,b] and two finite rational coefficient lists, the constructed unrounded payload passes the canonical cell checker. Empty lists are normalized to [0]; nonempty lists are preserved. The singleton-base Horner parser returns exactly the evenized normalized lists.")),
                    Paragraph(Text("With B=2R+|s|+1, let Ap,Aq be the Horner amplitude budgets and Dp,Dq their slope budgets. The norm-square width is at most Cl(b-a)+Ce*2^-m, where Cl=4Ap(18Ap/R+2Dp)+4Aq(18Aq/R+2Dq) and Ce=16(Ap^2+Aq^2).")),
                    Paragraph(Text("The two real component products use all four signed endpoint corners. Opposite endpoints enclose each translation difference, and the sign-safe square intervals are summed to form the exact norm-square payload."))),
                DescribeRole.Theorem)),
        []));
}

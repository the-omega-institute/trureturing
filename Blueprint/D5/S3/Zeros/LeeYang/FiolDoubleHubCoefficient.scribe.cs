using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class FiolDoubleHubCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical double-hub family: coefficient.",
        H("Double-hub coefficient"), Blocks(
            Paragraph(Text("For each placement, the finite sum over endpoint choices reduces to products of U,V,W,H and 1+X. The two central edges, the two central-pendant classes, and the two pendant-pendant classes contribute their actual physical weights.")),
            Paragraph(Text("Their weighted aggregate is Q_d=H_2(A V^2+B U W+C(1+X)UV+D(1+X)^2 U^2)+H_3(EUV+G(1+X)U^2)+9H_4U^2, with A=2d^4, B=3d^2(d^2-1)/2, C=4d(d-1)(2d-1), D=2(d-1)(2d-3), E=8d(2d-1), and G=16(d-1). Thus the actual coefficient is 200 times 12^(2m) times R_m for every m>=1 and cutoff>=3.")),
            Paragraph(Text("These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.")),
            Describe.Lean(DescribeId.Create("fioldoublehubcoefficient-actual-coefficient-identity"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubCoefficient.actual_coefficient_identity"), H("actual coefficient identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Connects the independently defined source coefficient and closed R polynomial using all placements and actual normalization. Exact source statement: theorem actual_coefficient_identity (m cutoff : \u2115) (hm : 1 \u2264 m) (hc : 3 \u2264 cutoff) :     sourceCoefficient m cutoff = Polynomial.C (200*(12:\u211d)^(2*m))*R m."))), DescribeRole.Theorem))));
}

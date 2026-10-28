using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfBalancedCfcBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfBalancedCfcBridge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual CFC derivative inequality for the balanced noncommutative two-level supplier.",
        H("The balanced certificate for actual CFC derivatives"),
        Blocks(
            Describe.Lean(DescribeId.Create("hsf-balanced-cfc-actual-twolevel-supplier"),
                DeclarationHandle.Create(Module + ".actual_twoLevel_supplier"),
                H("The actual two-level derivative supplier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let m and n be arbitrary finite index types, A and H "
                        + "square complex blocks and C an arbitrary m by n complex block. "
                        + "Assume S=[A,C;C star,H] is positive semidefinite, r is positive, "
                        + "and Z is Hermitian. Put P0=diag(I,rI), Y=P0 cubed and "
                        + "K=[A,r sqrt(r) C;r sqrt(r) C star,r cubed H]. The positive "
                        + "CFC cube root P=Y^(1/3) is exactly P0, and its actual matrix "
                        + "inverse is diag(I,r inverse I). Define F(t)=P inverse "
                        + "CFC.rpow(Y+tK,2/3) P inverse and B_j=F^(j)(0)/j factorial. "
                        + "These coefficients are genuine derivatives of the actual CFC function.")),
                    Paragraph(Text("The conclusion is 0 <= kappa(r) pairEnergy(A,C,H)/6 "
                        + "<= tr(B_3)+2 tr(Z B_2)+tr(B_1 Z Z)-(5/48) tr(B_1 cubed), "
                        + "where tr is real trace. The coefficient kappa and pairEnergy "
                        + "are the explicit quantities in HsfBalancedSpectralCertificate. "
                        + "No derivative, Taylor recurrence or desired inequality is a "
                        + "hypothesis. The direction S may be singular; repeated levels "
                        + "r=1, unequal block multiplicities and empty finite blocks are included.")),
                    Paragraph(Text("The proof uses Mathlib's positive diagonal and CFC power "
                        + "composition identities to establish positivity and the actual root "
                        + "and inverse. RpowPencilTaylor supplies the smooth root and its "
                        + "first three factorial-normalized ordered recurrences. Expanding "
                        + "the normalized two-thirds jet at orders one, two and three gives "
                        + "the three matrices in supplier_of_cubic_recurrence, which is "
                        + "then applied without commuting any matrix factors."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is a connection of classical finite dimensional CFC and "
                + "inverse-function calculus to the finite weighted Gram certificate. "
                + "The surrounding research target is He–Saunderson–Fawzi, "
                + "arXiv:2502.05627v1 Conjecture 6.2 / DOI 10.1007/s10107-025-02314-0 "
                + "Conjecture 1. No literature novelty or all-alpha, arbitrary-Y or "
                + "independent-X,Y compatibility theorem is claimed.")),
            Paragraph(Text("The full-telescope typed registration attempt is compiled "
                + "separately from the mathematical proof. Source-selection binding "
                + "remains unfinished under https://github.com/the-omega-institute/"
                + "trureturing/issues/23103; declared_validated is not claimed.")))));
}

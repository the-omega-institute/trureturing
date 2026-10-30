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
            Describe.Lean(DescribeId.Create("hsf-balanced-cfc-transported-twolevel-supplier"),
                DeclarationHandle.Create(Module + ".transported_twoLevel_supplier"),
                H("Transport by a common scale and fixed unitary coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Choose any equivalence q from the two block index types "
                        + "onto an arbitrary finite index type, any unitary U there, and "
                        + "any positive real c. The star-algebra equivalence spectralFrame "
                        + "reindexes by q and then conjugates by U. With e=spectralFrame(q,U), "
                        + "replace Y and K simultaneously by c e(Y) and c e(K). The same "
                        + "inequality holds for every Hermitian Z in the new coordinates, "
                        + "using real traces of the actual derivatives in those coordinates.")),
                    Paragraph(Text("The consumed transport proof establishes the actual "
                        + "CFC homogeneity and covariance identities for powers 1/3 and 2/3, "
                        + "identifies the actual inverse of the transported root, and "
                        + "cancels c^(2/3) against two factors c^(-1/3). The entire normalized "
                        + "function is conjugated by the fixed continuous real linear "
                        + "coordinate equivalence. This equivalence commutes with the "
                        + "factorial-normalized actual derivatives, and reindexing and "
                        + "unitary conjugation preserve real trace and Hermiticity. "
                        + "Arbitrary nonunitary congruence is outside this result.")),
                    Paragraph(Text("The theorem is parameterized by the chosen finite split, "
                        + "q, U, c and r. It does not construct such coordinates from a bare "
                        + "hypothesis that an input matrix has at most two eigenvalues. "
                        + "In the displayed frame, the center has positive levels c and "
                        + "c r cubed. No three-level or arbitrary-spectrum inequality "
                        + "follows from this result."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is a connection of classical finite dimensional CFC and "
                + "inverse-function calculus to the finite weighted Gram certificate. "
                + "The surrounding research target is He–Saunderson–Fawzi, "
                + "arXiv:2502.05627v1 Conjecture 6.2 / DOI 10.1007/s10107-025-02314-0 "
                + "Conjecture 1. No literature novelty or all-alpha, arbitrary-Y or "
                + "independent-X,Y compatibility theorem is claimed.")),
            Paragraph(Text("The two full-telescope typed registration attempts are compiled "
                + "separately from the mathematical proof. Source-selection binding "
                + "remains unfinished under https://github.com/the-omega-institute/"
                + "trureturing/issues/23103; declared_validated is not claimed.")))));
}

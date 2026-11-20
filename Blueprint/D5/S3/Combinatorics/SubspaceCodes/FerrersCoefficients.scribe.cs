using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class FerrersCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients";
    private const string Digest = "The coefficients recover the full parameter tuple and enforce the two support cuts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Coefficient recovery and support"), Blocks(
            Node("parameters", "Params", "Parameter space", DescribeRole.Definition,
                "For intermediate fields K and L of E over F, the parameter space is L⁴ × K. The entries are embedded in E when used as coefficients."),
            Node("parameter-coefficients", "paramCoefficients",
                "Linear coefficient map", DescribeRole.Definition,
                "Over a finite base field F of order q, put δ = b^(q³) − b for b in E. At parameters (u,a₁,a₂,ℓ,k), the map takes a₃ = δ⁻¹(ℓ + ck − bu) and returns (u − a₃,a₁,a₂,a₃). The map is defined for all b and c in E."),
            Node("param-coefficients-injective", "paramCoefficients_injective",
                "Recovery of the five parameters", DescribeRole.Theorem,
                "Let K ≤ L be intermediate fields of E over the finite field F. If β is a four-vector K-basis of E whose first two vectors span L over K, and δ is nonzero, the coefficient map with c = β(2) is injective. The coordinate along β(2) separates ℓ from ck."),
            Node("evaluation-on-k", "evaluation_on_K",
                "Evaluation on the first input block", DescribeRole.Theorem,
                "In a finite extension E of a finite field F of order q, if K has degree three over F, then f(x) = ux + a₁x^q + a₂x^(q²) for every x in K and arbitrary b and c in E."),
            Node("evaluation-on-b-k", "evaluation_on_bK",
                "Evaluation on the second input block", DescribeRole.Theorem,
                "In a finite extension E of a finite field F of order q, if K has degree three over F and δ is nonzero, then f(bx) = (ℓ + ck)x + a₁(bx)^q + a₂(bx)^(q²) for every x in K and arbitrary c in E."))));

    private static DocumentBlock Node(string id, string declaration, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Gid + "." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}

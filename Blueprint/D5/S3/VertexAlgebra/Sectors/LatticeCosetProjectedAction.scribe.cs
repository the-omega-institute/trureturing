using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetProjectedActionDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("coset-projected-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetProjectedAction", H("Finite transverse target action"), Blocks(
            D("polynomialMode", "For any complex module V, any integer-indexed family A with values in V, and integer m, the complex linear polynomial functional sending monomial(j,z) to z times A(m-j). This is a finite coefficient sum, with no truncation hypothesis on A.", DescribeRole.Definition),
            D("scalarTranslation", "For every external integral source a, the complex algebra homomorphism evaluating each transverse variable (j,k) at minus transversePair(a,j) times the polynomial variable to power k+1. It is the transverse part of native annihilation translation followed by longitudinal projection.", DescribeRole.Definition),
            D("projected_transverse_polynomial", "For positive definite original D with arbitrary finite rank and external rank, integral B, symmetric even-diagonal C, arbitrary external source a, arbitrary selected output sector d, every original source state u, every transverse polynomial h, integer mode m and every ambient target state v: project the complete native mode Y_E(J_a u)[m] applied to h(T)v. This equals polynomialMode at m, using the family t maps to P_d(Y_E(J_a u)[t]v), evaluated on scalarTranslation(a,h). Thus each inverse-power coefficient of the native transverse substitution shifts the complete longitudinal mode by its negative index. Every source descendant and every target polynomial is included. The proof inducts on h using the all-state transverse commutator; the sums are finite polynomial sums.", DescribeRole.Theorem),
            Paragraph(Text("The native lattice conventions are those of Bakalov-Kac, math/0402315v1, section 4.1. The formula applies in particular to arbitrary longitudinal states multiplied by transverse creation coefficients, supplying the outer-source substitution needed in the two-source comparison. LatticeCosetOperatorCorrection combines this arbitrary-target action with the inner all-state creation expansion and exact binomial coefficient. No ambient positivity or scalar-cocycle replacement is used.")))));
}

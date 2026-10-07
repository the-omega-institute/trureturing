using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

// Scalar identities are repository-derived;
// the motivating paper acknowledgement is not an attribution of its solution.
internal sealed class P13ScalarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Scalar.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit finite-coefficient q-series solve the scalar bulk recurrence by uniform formal annihilation.",
        H("Explicit P13 scalar q-series and minimality"),
        Blocks(
            Node("p13-scalar-den", "Finite denominators", "Den", "Den(r) is the product of 1-X^i for i=1 through r; Den(0)=1.", DescribeRole.Definition),
            Node("p13-scalar-deninv", "Lawful denominator inverses", "DenInv", "DenInv(r) uses the proved constant coefficient one and the existing formal-series unit inverse.", DescribeRole.Definition),
            Node("p13-scalar-deninv-succ", "Successor cancellation", "DenInv_succ", "For every r, multiplying DenInv(r+1) by 1-X^(r+1) gives DenInv(r).", DescribeRole.Theorem),
            Node("p13-scalar-e-rescale", "The independent coefficient series", "E_rescale", "The formal v-series with coefficients DenInv(r) satisfies E(Xv)=(1-v)E(v).", DescribeRole.Theorem),
            Node("p13-scalar-s", "Explicit finite convolution", "S", "S(k) is the sum over r=0 through k of DenInv(r) times DenInv(k-r).", DescribeRole.Definition),
            Node("p13-scalar-s-one", "The first convolution boundary", "S_one", "The exact boundary is (1-X)S(1)=2, with S(0)=1.", DescribeRole.Theorem),
            Node("p13-scalar-s-recurrence", "The universal convolution recurrence", "S_recurrence", "For every natural k, (1-X^(k+2))S(k+2)=2S(k+1)-S(k). The proof squares the rescale identity.", DescribeRole.Theorem),
            Node("p13-scalar-c-one", "The separate signed boundary", "c_one", "For c(k)=(-1)^k X^choose(k,2) S(k), the k=1 boundary is (1-X)c(1)=-2.", DescribeRole.Theorem),
            Node("p13-scalar-c-recurrence", "Signed higher coefficients", "c_recurrence", "For every natural k, (1-X^(k+2))c(k+2)=-2X^(k+1)c(k+1)-X^(2k+1)c(k).", DescribeRole.Theorem),
            Node("p13-scalar-phi", "Finite coefficient Phi", "Phi", "Phi(j) is defined coefficient by coefficient using the finite sum of c(k) point(j)^k for k=0 through the requested coefficient degree.", DescribeRole.Definition),
            Node("p13-scalar-phi-constant", "Phi has constant coefficient one", "constantCoeff_Phi", "For every natural j, Phi(j) has constant coefficient one.", DescribeRole.Theorem),
            Node("p13-scalar-phi-difference", "The exact cleared q-difference", "Phi_difference", "For every natural j, delta squared times Phi(j) equals delta times (delta-2X^(j+1)) times Phi(j+1), minus X^(2j+3) times Phi(j+2).", DescribeRole.Theorem),
            Node("p13-scalar-w-shift", "Derived W shift", "W_shift", "Any ordinary power-series family satisfying the section 6 bulk recurrence has W(j)=-X^(j+2)deltaInv W(j+1) for j at least two. This is derived from the explicit Phi difference.", DescribeRole.Theorem),
            Node("p13-scalar-w-annihilator", "The uniform annihilator", "W_uniform_dvd", "For every n and every j at least two, X^n divides W(j), with only the bulk recurrence as a hypothesis.", DescribeRole.Theorem),
            Node("p13-scalar-minimal", "The formal minimal-solution lemma", "minimal_solution", "For any power-series family h satisfying Bulk(h), and every j at least two, delta Phi(j)h(j)+X^j Phi(j+1)h(j-1)=0. Every coefficient vanishes by the uniform annihilator; no tail or finite-height premise is assumed.", DescribeRole.Theorem),
            Node("p13-scalar-d-unit", "Lawful scalar denominator inversion", "D_mul_DInv", "For D=delta(1-2X-X squared)P-X cubed(1+X)R, the proved inverse identity is D times DInv equals one.", DescribeRole.Theorem),
            Node("p13-scalar-g", "The explicit scalar series", "G", "G=1+X(1-X) cubed P times the unit inverse of D. P=Phi(1), R=Phi(2), and delta=(1-X) squared. P13Enumeration.actual_A_eq_G proves that this explicit series equals the actual matching series after the lawful substitution X/(1+X) squared. P13Enumeration.actualSeries_eq_G_subst_q recovers the original counting series by substituting the Catalan series minus one.", DescribeRole.Definition),
            Node("p13-scalar-g-cleared", "The scalar cancellation", "G_cleared", "The defined series satisfies (G-1)D=X(1-X) cubed P.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

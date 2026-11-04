using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostConformalBRSTStateDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string text,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create("bc-conformal-brst-state-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conformal and cubic-current states of the original occupation ghost fields.",
        H("Original bc conformal state and cubic-current zero mode"), Blocks(
            Paragraph(Text("These are the classical algebraic bc ghost formulas in the original finite-occupation Fock representation, with b vacuum cut at minus one and c cut at two. The conventions follow Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. The proofs use the existing original all-state Y and signed integer iterate; no abstract replacement state-field map or transported charge is introduced.")),
            Node("Omega", "The explicit conformal state",
                "Omega is minus twice ket{0,3} plus ket{1,2}, equivalently minus twice b(-2)c(0)vacuum minus b(-3)c(1)vacuum. The sorted-occupation signs and original mode shifts are retained.", DescribeRole.Definition),
            Node("Jg", "The explicit raw odd cubic-current state",
                "Jg is ket{0,1,3}, literally b(-2)c(1)c(0)vacuum. There is no improvement term.", DescribeRole.Definition),
            Node("conformal_modes", "Every integer conformal mode is the original Virasoro mode",
                "For every integer m, the (m+1)-st mode of Y(Omega) equals the original BcGhostVirasoro.L(m). The two negative-residue normal products are reindexed on their actual statewise finite integer half-lines. Their coefficients combine to the literal weight m+q in the original normal-ordered bilinear sum."),
            Node("current_odd", "Actual odd parity of the cubic state",
                "Parity sends the sorted three-occupation state Jg to minus Jg. This supplies the odd sign in the zero-residue identity and is consumed in the current comparison and signed derivation."),
            Node("current_zero_mode", "The current zero mode is the entire original cubic charge",
                "The zero mode Y(Jg)[[0]] equals the complete original locally finite sum over integer pairs (p,q), with coefficient one half times (p-q) and the original normal ordering of c(p)c(q)b(-p-q). Its anticommutators on all b and c modes follow from actual generator contractions and the zero-residue iterate. The difference from Qg anticommutes with the generators; composing with parity gives an ordinary commutant, to which scalar_commutant legitimately applies. Vacuum vanishing removes the scalar, and parity involution removes the composition."),
            Node("Qg_signed_derivation", "Signed derivation on every actual homogeneous-state field mode",
                "For every original Fock state a, every natural parity exponent p with parity(a)=(-1)^p a, and every integer n, Qg Y(a)[[n]] minus (-1)^p Y(a)[[n]] Qg equals Y(Qg a)[[n]]. This is an operator equality on the full original finite-occupation carrier. The signed integer iterate at residue zero collapses to its i=0 terms; the actual current equality and odd parity identify the operator with Qg. No ambient square-zero, rank-26 or matter-plus-ghost premise is used."),
            Paragraph(Text("The pure ghost charge is anomalous: no nilpotence is asserted. These results do not establish a total coupled BRST system, BRST cohomology, a no-ghost theorem, Monster moonshine, string dynamics or AdS/CFT. Native verification, independent review and official admission are distinct statuses.")))));
}

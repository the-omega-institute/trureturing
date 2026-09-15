using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PrimeRectangleTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual residue-prefix caps transfer weighted second moments of arbitrary finite layers.",
        H("Weighted Residue-Prefix Rectangle Moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-rectangle-joint-second-moment"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Congruence/PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le"),
            H("An explicit bound for the actual joint rectangle load"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let X and I be finite types and p and H natural numbers. The old "
                    + "weights mu(x) and all layer coefficients A(e,i,x) are nonnegative. "
                    + "At each old point x, K(x,y) is a nonnegative probability distribution "
                    + "on Fin(p^H). For every depth t from one through H, every residue "
                    + "r and every x, assume the K-mass of y mod p^t = r mod p^t is at "
                    + "most M(t,x). This envelope may depend on both t and x.")),
                Paragraph(Text(
                    "Assume the zero layer's mu-weighted second moment is at most G0. "
                    + "For every positive depth t and each exponent e at most t, assume "
                    + "the second moment of the layer sum over I, weighted by mu(x)M(t,x), "
                    + "is at most G(t,e). Thus each old layer has its own bound at each prefix depth. "
                    + "Choose arbitrary natural residues b(e,i). The new "
                    + "load sums A(e,i,x) over those pairs whose residue condition "
                    + "y mod p^e = b(e,i) mod p^e holds. Its squared expectation under "
                    + "mu(x)K(x,y) is at most G0 plus the sum, for t from one through H, "
                    + "of the sum of G(t,e) over e from zero through t, plus t times G(t,t).")),
                Paragraph(Text(
                    "The proof bounds each actual intersection by its deeper cylinder, "
                    + "derives nonnegativity of the prefix envelope from the kernel, "
                    + "and controls cross-layer moments by weighted Young's "
                    + "inequality. Kernel normalization handles the zero-exponent pair "
                    + "without distortion. For each pair with maximum t, the two layer-specific "
                    + "moment bounds enter with weight one half. An induction sums these weights, "
                    + "retaining the contribution of the same zero layer in all its cross terms.")),
                Paragraph(Text(
                    "If all old layers at depth t use the same bound Gt, the result "
                    + "specializes to G0 plus the sum of (2t+1)Gt. If the zero layer "
                    + "instead has bound Dt, while every positive old layer has bound "
                    + "Gt, the contribution is Dt+2tGt. This retains information about "
                    + "the particular old layout shared by the zero-to-positive crosses; "
                    + "no separate wrapper theorem is needed.")),
                Paragraph(Text(
                    "The statement includes H = 0. It needs neither primality of p, "
                    + "normalization of mu, independence from x, nor compatible choices "
                    + "of the test residues. This is the rectangle estimate used in "
                    + "joint-load arguments for distinct covering systems. Constructing "
                    + "the probability kernel and embedding a divisor layout by the "
                    + "Chinese remainder theorem are separate proof obligations; this "
                    + "theorem does not settle the odd covering problem."))),
            DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualC2Document : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/Lattice/ActualC2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative-norm charge collapses the literal C2 space of every actual lattice state.",
        H("Full-State Negative-Norm C2 Collapse"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lattice-actual-c2-negative-norm-collapse"),
                DeclarationHandle.Create(Prefix + "negative_norm_c2_eq_top"),
                H("Negative-norm full-state C2 collapse"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary finite-rank symmetric integral even lattice datum, "
                            + "C2 is the literal complex submodule spanned by mu(a,-2,b) for "
                            + "all Carrier states a and b. If a charge has negative bilinear "
                            + "norm, this full-state C2 is the whole carrier.")),
                    Paragraph(Text(
                        "The proof first inducts on every higher negative mode using actual "
                            + "state differentiation and division by the nonzero integer "
                            + "coefficient. It then applies the genuine integer commutator at "
                            + "p=-1 and q=-2 to generators and extends the result through "
                            + "the literal span, so left multiplication by every actual state "
                            + "at mode -1 preserves C2.")),
                    Paragraph(Text(
                        "The ground pair of charges alpha and -alpha at mode "
                            + "bilinear(alpha,alpha)-1 has normalized coefficient epsilon, "
                            + "hence puts the actual vacuum in C2. Actual creation at mode -1 "
                            + "then puts every state in C2. This uses the original actual "
                            + "normalized Y modes and arbitrary mixed-charge oscillator states; "
                            + "it is not the restricted norm-four cyclic-vacuum C2 result.")),
                    Paragraph(Text(
                        "As a scientific application, combined with the delivered negative "
                            + "rank-one no-finite-strong-generation result, the full quotient can "
                            + "be zero while finite strong generation still fails in its exact "
                            + "finite right-nested negative-word convention. Ground weights "
                            + "-d*s^2 are unbounded below, identifying the missing well-founded "
                            + "weight descent in the usual lifting argument. The rank-one source "
                            + "at commit 95e370f49206cf3a48f06ece62ef0307e3990bc0 is a pending "
                            + "separate supplied result when it is absent from the current dev "
                            + "tree; it is not imported here. No arbitrary-bracketing equivalence "
                            + "or literature novelty claim is asserted."))),
                DescribeRole.Theorem))));
}

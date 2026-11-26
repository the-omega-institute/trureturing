using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicMatchedOccupationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicMatchedOccupation.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared Hellinger distance controls the excess of the cubic energy over its endpoint collapse.",
        H("Cubic energy at matched occupation"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-probability-comparison"),
                DeclarationHandle.Create(Owner + "finite_probability_comparison"),
                H("Weighted cubic deficits of finite probability laws"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Let P and Q be nonnegative laws of total mass one on the same finite set, " +
                        "and let u,v > 0. Put C(u,v) = 4(u+v)/9 + 16uv/[9(u+v)]. Then " +
                        "C(u,v)(1 − ∑ᵢ√(PᵢQᵢ)) ≤ u(1 − ∑ᵢ Pᵢ^(1/3)Qᵢ^(2/3)) + " +
                        "v(1 − ∑ᵢ Pᵢ^(2/3)Qᵢ^(1/3)). Zero entries are allowed.")),
                    Paragraph(Text("Writing the pointwise weighted arithmetic–geometric mean deficits in " +
                        "the sixth roots of the two masses gives a sum of nonnegative terms. Summing " +
                        "the resulting inequality and using the two unit masses gives the comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generator-energy-sub-matched-occupation-ge"),
                DeclarationHandle.Create(Owner + "generator_energy_sub_matched_occupation_ge"),
                H("Excess over the true endpoint masses"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("In the cubic case of Wu v1, Remark 3.15, let D be positive definite and ρ " +
                        "positive semidefinite on a finite complex matrix space. Take a finite family of " +
                        "jumps Jₖ with rates aₖ,bₖ > 0 and D Jₖ D⁻¹ = (aₖ/bₖ)Jₖ. Assume both " +
                        "Aₖ = Re Tr(ρ JₖJₖ†) and Bₖ = Re Tr(ρ Jₖ†Jₖ) are positive for every k.")),
                    Paragraph(Text("Write λᵢ for the eigenvalues of ρ and wₖᵢⱼ for the squared modulus of " +
                        "the jump entry in that eigenframe. The endpoint laws are Pₖᵢⱼ = wₖᵢⱼλᵢ/Aₖ " +
                        "and Qₖᵢⱼ = wₖᵢⱼλⱼ/Bₖ. Set xₖ = bₖAₖ, yₖ = aₖBₖ, " +
                        "uₖ = xₖ^(1/3)yₖ^(2/3), and vₖ = xₖ^(2/3)yₖ^(1/3). The cubic kernel is " +
                        "K₃(x,y) = x + y − x^(1/3)y^(2/3) − x^(2/3)y^(1/3).")),
                    Paragraph(Text("Set G = D^(1/6), H = D^(−1/6), M = ρ^(1/3), and X = HMH. " +
                        "Use L(X) = ∑ₖ[2aₖ K(Jₖ,X) + 2bₖ K(Jₖ†,X)] with " +
                        "K(V,X) = ((V†V)X + X(V†V))/2 − V†XV. The ordinary cubic energy " +
                        "(9/8) Re Tr(M² G L(X) G) minus (9/4)∑ₖ K₃(xₖ,yₖ) is at least " +
                        "(9/4)∑ₖ C(uₖ,vₖ)(1 − ∑ᵢⱼ√(PₖᵢⱼQₖᵢⱼ)).")),
                    Paragraph(Text("The spectral expansion identifies the endpoint totals with the two " +
                        "jump traces. Subtracting the collapsed energy leaves the two weighted cubic " +
                        "deficits of the normalized laws. For signed lowering jumps the endpoint traces " +
                        "are the empty- and occupied-mode masses. In a diagonal product with those " +
                        "marginals, the common spectator probabilities factor out by homogeneity."))),
                DescribeRole.Theorem))));
}

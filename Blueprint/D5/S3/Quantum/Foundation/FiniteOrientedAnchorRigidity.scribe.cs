using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteOrientedAnchorRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite oriented anchors determine an arbitrary complete actual output.",
        H("Finite oriented anchor rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-oriented-anchor-rigidity"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteOrientedAnchorRigidity.finite_oriented_anchor_rigidity"),
            H("Complete intensity and one-sided anchor comparisons force linear isometry"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be a complex Hilbert space of dimension d at least one, with a specified orthonormal basis a indexed by Fin d. Let E be the finite complete outcome menu, and let W_e be finite-dimensional complex Hilbert spaces. The output PiLp 2 W is their Hilbert direct sum, so its squared norm is the sum of the squared channel norms. Write F_e(x)=(F(x))_e for a single arbitrary function F on all of H. No additivity, homogeneity, continuity, linearity, output-anchor orthogonality or input-dependent phase convention is assumed.")),
                Paragraph(Text("For every x in H, require sum_e ||F_e(x)||^2=||x||^2. For each basis index j and k in {0,1,2,3}, require F_e(i^k a_j)=i^k F_e(a_j) in every channel, and sum_e ||F_e(x)-F_e(i^k a_j)||^2 <= ||x-i^k a_j||^2 for every input x. The k=0 calibration is the identity. Thus the calibration is exactly the three nonzero orientations in Definition 3.1, and the comparisons use exactly the four anchors in Definition 3.2 of AURIC v80. Neither condition is extended to arbitrary phase rotations or arbitrary comparison pairs.")),
                Paragraph(Text("The inner product is conjugate linear in its first slot and linear in its second slot. Expanding the two squared distances with equal diagonal norms bounds the real part of <F(x),i^k F(a_j)> from below by that of <x,i^k a_j>. The opposite orientations give both inequalities for the real coordinate, and the two quarter turns give both inequalities for the imaginary coordinate. Consequently <F(x),F(a_j)>=<x,a_j> for every x and j. Conjugation gives the source convention <F(a_j),F(x)>=<a_j,x>. Taking x=a_i proves orthonormality of the output anchors.")),
                Paragraph(Text("Define L by sending a_j to F(a_j), using basis extension. The orthonormality just proved makes L a complex linear isometry V. Basis reconstruction and the anchor-coordinate equalities give <F(x),V(x)>=<x,x>. Together with the two equal norms this gives ||F(x)-V(x)||^2=0. Hence F(x)=V(x) on all inputs, including zero and arbitrary unnormalized vectors. Pointwise agreement makes V unique. The finite Hilbert adjoint satisfies V* V=I.")),
                Paragraph(Text("This is Theorem 5.1 with the complete-record interpretation of Definitions 2.1 through 3.2. The Hilbert-space and shared-reference interface is a premise; the theorem supplies no construction of that interface from physical history. Every outcome, including failure and stopping records, must be included in E. A Hilbert direct sum represents the complete record mathematically and does not grant actual coherent control between different outcome labels. The same F is used throughout, without postselection or separate phase choices for different inputs.")),
                Paragraph(Text("Full pairwise complex inner products and distances, complex linearity and continuity follow from F=V and the standard linear-isometry properties. The conclusion is on all of H, rather than only the unit sphere of Proposition 5.3. The dimension d is a natural number with the literal premise 1<=d; no dimension truncation is used. The norm expansion, basis reconstruction, orthonormal-basis isometry constructor and adjoint identity use Mathlib's existing results. The finite-anchor argument supplies their geometric hypotheses; no separate novelty claim is made for those general results."))),
            DescribeRole.Theorem))));
}

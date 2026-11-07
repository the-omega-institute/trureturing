using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis;

internal sealed class ReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Torsion-safe reconstruction of every original physical coordinate — UNCOMPILED source preparation.",
        H("Torsion-safe reconstruction of every original physical coordinate"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-selected-upper-reconstruction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Reconstruction.actual_selected_upper_reconstruction"),
                H("actual selected upper reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proved low table and high form leave four group parameters. Combining the actual Q and 8Q rows with the affine row forces x=2u by a unit coefficient. Integral Bezout identities then recover u=ac, y=-sc and theta=Qc. Every original coordinate is its primitive integer weight times c=-3X00+2X20, from only selected annihilation."))), DescribeRole.Theorem),

            Paragraph(Text("Four parameters from the actual selected presentation. The source combines the physical high descent, T0,T1 and the actual low table to derive the shared first, middle and last normal form with rho=0. Its parameters are u=f0, x=f1, y=g0 and theta=2g_(d-3)-g_(d-2), and its remaining slope is (s/2)x+ay=0. No annihilation of all zero subsets is assumed; SelectedAnnihilates names exactly the 3d-1 actual upper indicators.")),
            Paragraph(Text("The actual terminal combination kills low torsion. The sealed integral_read is reused on this derived normal form. The selected chi(Q) and chi(8Q) rows give Dq=u+floor(Lq/2)x+Mq y-theta=0 and D8=floor(L8/2)x+M8 y+2theta=0. The integer definitions prove 2Lq+L8=5s and 2Mq+M8=5a, with Lq odd and L8 even. Consequently D8+2Dq-5R_a=2u-x. Its coefficient -1 determines x=2u in every abelian group. This step handles the remaining 2-primary torsion directly.")),
            Paragraph(Text("Bezout reconstruction and the prescribed generator. The slope becomes su+ay=0. Since 2s-5a=1, the element c=-5u-2y satisfies u=ac and y=-sc; then x=2ac. The Q-row, together with aLq-sMq=Q, gives theta=Qc. The existing scaled_first, scaled_middle, scaled_last and primitive_place lemmas translate the normal form into X_i=primitive_i*c on every original Fin(3d) label. T0 identifies c with exactly -3X_(0,0)+2X_(2,0).")),
            Paragraph(Text("Mathematical relevance. For a zero-incidence presentation, reconstruction in arbitrary abelian groups is what excludes finite torsion in the quotient. The selected masks provide a small exact integral presentation of the primitive rank-one weight quotient. A permutation preserving the complete zero-incidence hypergraph acts on the relation lattice and its quotient; the selected family is a presentation, and is not asserted to be invariant under that permutation action.")),
            Paragraph(Text("Status and provenance. actual_selected_upper_reconstruction is retained as a load-bearing candidate source script and is consumed by Result on the quotient of the actual selected span. The argument follows the supplied torsion-safe direct reconstruction answer and its completed ordinary review, with repository prior disclosed. That review does not validate Lean. All source and sealed additive dependencies remain UNCOMPILED; no kernel, official or publication claim is made."))), []));
}

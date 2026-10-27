using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourTensorCommutantModesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every integer mode of every state of the literal commutant intertwines the actual minus-one tensor map.",
        H("Commutant Modes on the Actual Tensor Product"),
        Blocks(
            Paragraph(Text("Let D be arbitrary production lattice data, a any charge, and s any complex scalar. "
                + "Let S=NormFourVacuumIrreducible.vacuumDescendants(D,a,s) and C=NormFourCommutant.space(D,a,s), "
                + "with their actual inclusions into Carrier(D). Let V_C=NormFourCommutant.restrictedVertexAlgebra(D,a,s). "
                + "Use exactly the existing complex-linear map F=NormFourTensorEmbedding.tensorMap(D,a,s), "
                + "whose pure-tensor value is F(u tensor c)=Y(c)_(-1)u. The tensor product is the algebraic tensor product over the complex numbers.")),
            Describe.Lean(
                DescribeId.Create("normfour-actual-commutant-mode-intertwining"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourTensorCommutantModes.actual_commutant_mode_intertwining"),
                H("All commutant states, all integer modes and all tensors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every b in the whole C, every integer q, and every z in the whole S tensor C, "
                    + "F((id_S tensor (V_C.stateField(b))_q)z)=Y(b)_q F(z). "
                    + "There is no equation on the norm of a or the scalar s, and no assumed commutation or intertwining identity."))),
                DescribeRole.Theorem),
            Paragraph(Text("The equality NormFourFullCommutant.space_eq_full_state_commutant implies Y(u)_j c=0 "
                + "for every u in S, c in C and j at least zero. Thus the complete actual mode commutator "
                + "[Y(u)_(-1),Y(c)_n] is zero for every integer n: each natural-indexed commutator term contains Y(u)_j c. "
                + "When n is nonnegative, applying this equality to the actual ambient vacuum and using creativity and creation gives Y(c)_n u=0.")),
            Paragraph(Text("Apply the actual state-field iterate to b,c,u with r=q and n=-1. Its complete first family has terms "
                + "(-1)^i choose(q,i) Y(b)_(q-i) Y(c)_(i-1)u, for all natural i. Every term with i different from zero vanishes "
                + "by the preceding nonnegative-mode identity. Mathlib's finsum_eq_single reduces this entire family to its zeroth term "
                + "Y(b)_q Y(c)_(-1)u. The complete second family has terms "
                + "(-1)^i choose(q,i) Y(c)_(q-1-i) Y(b)_i u; every term vanishes. "
                + "The actual iterate therefore gives Y(Y(b)_q c)_(-1)u=Y(b)_q Y(c)_(-1)u for every integer q.")),
            Paragraph(Text("The coefficient inclusion in NormFourCommutant.actual_closure identifies the actual value of every V_C coefficient "
                + "with its ambient Y coefficient. The pure-tensor formula for the existing F now gives the claimed equality on u tensor c. "
                + "Tensor-product induction extends it to every tensor by linearity, including zero and arbitrary finite sums.")),
            Paragraph(Text("The tensor map and its pure-tensor formula belong to NormFourTensorEmbedding; its original injectivity, S-side identity "
                + "and vacuum-line theorem retain their norm-four and sign hypotheses. The full-state equality belongs to NormFourFullCommutant, "
                + "and the actual commutant vertex algebra and coefficient inclusion belong to NormFourCommutant. "
                + "The full iterate is LatticeAllStateReconstruction.stateField_iterate in LatticeAllStateLocality, "
                + "and the commutator is LatticeActualStateFieldCalculus.mode_commutator. "
                + "The imported lattice fields retain Bakalov-Kac, math/0402315, section 4.1 attribution. "
                + "The norm-four construction retains Dong-Mason-Zhu, Theorem 6.3 and Shimakura, arXiv:1202.6107, (1.3) attribution. "
                + "The residue sources retain their Carnahan and Matsuo-Nagatomo attribution and license notices. "
                + "This result constructs no tensor vertex algebra and asserts no surjectivity or ambient factorization. "
                + "It makes no literature novelty, rationality, fusion, Monster, analytic CFT, string-theory or AdS/CFT claim.")))));
}

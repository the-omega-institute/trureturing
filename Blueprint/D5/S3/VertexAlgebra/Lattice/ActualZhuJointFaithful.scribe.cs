using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuJointFaithfulDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuJointFaithful", H("Actual joint bottom faithfulness"), Blocks(
            Paragraph(Text("Let D have arbitrary natural rank, symmetric integral Gram matrix and even diagonal, with positive-definite real Gram matrix. Q is the original full Carrier modulo literal zhuO. Every dual-coset bottom retains all tied minimizing charges, including rank zero. ActualZhuTransitionSpan supplies source spanning, and LatticeDualCosetZhuRepresentation supplies the native all-state action. Mature source: Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, https://arxiv.org/html/q-alg/9605032v1, Theorem 3.4 and Remark 2.11. The representation source attributes its module-residue adaptation to Fedor K. Popov, Lean_VOA at 013a799ca834a8a6b3afa8129e3e522025b3f45c under Apache-2.0. No classification, rationality, semisimplicity, dual-lattice cocycle extension, literature novelty or CFT/string-theory completion is asserted.")),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-current-action"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.current_action"), H("Actual current eigenvalues"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native representation of the literal quotient acts on each ground vector in a full minimum fiber with weight rep(c) plus G gamma. This is computed with action_current_coefficients, without assuming diagonal action."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-projector-action"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.projector_action"), H("Actual source projector images"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each finite source projector acts on every native minimum vector by one or zero according to equality of its full grid weight. The calculation evaluates pinned Mathlib Lagrange polynomials through the actual representation. Polynomial.algHom_ext identifies each polynomial algebra map with aeval at its image of X; Module.End.aeval_apply_of_mem_apply_eq_smul in Mathlib.LinearAlgebra.Eigenspace.Minpoly then evaluates on every eigenvector, including zero, without a nonzero-vector hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-ground-action"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.ground_action"), H("Nonzero native ground transition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any two tied minima of one class, the energy difference identity sets the actual shifted ground coefficient index to zero. The image of E_(gammaOut-gammaIn) on the input is precisely epsilon(gammaOut-gammaIn,gammaIn) times the output. The cocycle remains the original cocycle on integral charges."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-transition-matrix-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.transition_matrix_coefficient"), H("Distinct scalar matrix coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual bottom action coefficient at any component, input and output is epsilon for its matching source transition and zero for every other transition. Injectivity of the original cosetEquiv distinguishes different classes and input minima; original carrier basis coefficients distinguish outputs."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-joint-kernel-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.joint_kernel_zero"), H("Direct joint-kernel extraction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write an arbitrary class of the full literal quotient in the source transition span. Apply one actual bottom coefficient to this finite linear combination. The diagonal matrix coefficient identity and nonvanishing native epsilon force each source coefficient to vanish. No finite-dimensional or semisimplicity inference substitutes for this extraction."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-joint-injective"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.joint_injective"), H("Joint faithfulness on the whole literal quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of the actual bottom representations over every dual class is injective, by applying direct joint-kernel extraction to a difference. Every tied minimum is retained. The only lattice condition added to the native integral even data is positive definiteness, with rank zero and zero charge included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-bottom-basis-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.bottomBasis_apply"), H("The complete native bottom basis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native gradeCoeffEquiv is reindexed by bottom_fiber: a bottom label consists exactly of an arbitrary minimizing charge and zero oscillator occupation. Its transported basis vector equals the original ground vector used in every coefficient calculation. The readout in the joint-faithfulness proof consumes this full basis transport, so no selected subset of minima replaces the actual bottom."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-transition-linear-independent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.transition_linearIndependent"), H("Independence of the original source transitions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying each readout to a zero finite linear combination isolates its matching coefficient times the nonzero native epsilon. Thus every coefficient vanishes, proving linear independence in Q itself."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-source-basis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.sourceBasis"), H("The full literal quotient transition basis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source transition family is a complex basis of Q, indexed by the disjoint union over all discriminant classes c of Min_c times Min_c. Its independence follows from actual scalar coefficients and its spanning from ActualZhuTransitionSpan.source_transition_span. Both factors retain the complete minimum fiber."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-bottom-dimension"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.bottom_dimension"), H("Dimension of every entire bottom"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transported native basis identifies the complex dimension of each SectorBottom with Nat.card of its full minimum fiber. This identity supplies each summand in sharp_dimension."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhujointfaithful-sharp-dimension"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuJointFaithful.sharp_dimension"), H("Exact sum of squared bottom dimensions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual diagonal transition coefficients prove linear independence of the full source-transition family. Together with source_transition_span they give a basis of Q indexed by the finite disjoint union over c of Min_c times Min_c. The full native bottom basis has dimension equal to the cardinality of Min_c. Hence the dimension of Q equals the sum over c of the squared actual bottom dimensions. This consequence is proved after direct joint injectivity and is not used as its substitute."))), DescribeRole.Theorem))));
}

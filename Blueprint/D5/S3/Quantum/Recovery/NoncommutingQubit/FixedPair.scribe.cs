using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.NoncommutingQubit;

internal sealed class NoncommutingQubitFixedPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rigidity and tensor factorization from a recovered pair of noncommuting qubit states.",
        H("Noncommuting qubit fixed pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cptp-eq-id-of-noncommuting-fixed-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.cptp_eq_id_of_noncommuting_fixed_pair"),
                H("Rigidity of a noncommuting fixed pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(
                    Paragraph(Text("Let a completely positive trace-preserving map on complex two by two matrices fix two positive semidefinite trace-one matrices A and B with AB different from BA. The map equals the identity on the whole complex matrix algebra.")),
                    Paragraph(Text("Diagonalize the nonzero traceless Hermitian difference A minus B by a unitary. In this basis the map fixes the difference of the two rank-one coordinate projections. Their images have trace one and nonnegative diagonal entries. The fixed difference forces the weight on each opposite eigenline to vanish. Each such weight is a sum of squared Kraus entries, so both off-diagonal entries of every Kraus matrix vanish.")),
                    Paragraph(Text("Diagonal Kraus matrices act by entrywise scalar multiplication. Trace preservation gives diagonal multipliers equal to one. A must have a nonzero off-diagonal entry in this basis, since otherwise B would also be diagonal. Fixing A and using Hermiticity forces both other multipliers to be one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensor-form-of-noncommuting-qubit-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair.tensor_form_of_noncommuting_qubit_recovery"),
                H("Physical tensor form from two recovery equations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(
                    Paragraph(Text("Let Phi be a completely positive trace-preserving map from any finite complex matrix algebra to the qubit algebra. A completely positive trace-preserving recovery R restores two density matrices S and T from their noncommuting outputs. Suppose S is positive definite. Then Phi composed with R equals the identity on every qubit matrix.")),
                    Paragraph(Text("Use the represented Kraus families in the pointwise tensor theorem. Its support projection acts as the identity on R(Phi(S)) and hence equals the identity, because S is invertible. The resulting tensor isometry U is therefore unitary onto the whole physical input space. The environment operator kappa is positive definite and has trace one. For every qubit matrix Z, the recovery is U(kappa tensor Z)U*. In particular the two recovery equations identify both input states with products using the same kappa.")),
                    Paragraph(Text("Let Q be R of the qubit identity. The Kraus left-inverse relations give Q times the trace adjoint of Phi at Z equal to R(Z). The support calculation makes Q invertible. In the tensor coordinates, Q is U(kappa tensor identity)U*, so the trace adjoint of Phi at Z is U(identity tensor Z)U*. Pairing with every Z gives the physical partial trace over the environment."))),
                DescribeRole.Theorem))));
}

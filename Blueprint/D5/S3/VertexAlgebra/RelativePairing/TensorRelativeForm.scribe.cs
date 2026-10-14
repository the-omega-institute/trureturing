using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.RelativePairing;

internal sealed class TensorRelativeFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative preimages annihilate both native inserted-C0 boundary obstructions.",
        H("The actual tensor form and relative antighost kernel"),
        Blocks(
            Paragraph(Text("On the unrestricted algebraic matter tensor ghost State D, F is the actual matter hermitianForm times the energy-rotated Hplus on pure tensors. The physical C0 is C D 0, namely the tensor lift of c(0), or ghost currentMode .c (-2). Pi is the native tensor parity operator. Q is the original finite-support BRST charge. Both inverse-Gram equations are retained whenever its form adjoint is used.")),
            Describe.Lean(DescribeId.Create("tensor-relative-b-transpose"),
                DeclarationHandle.Create(Prefix + "F_B"), H("Actual antighost form transpose"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("F(B(mode) left,right)=F(Pi left,B(-mode) right) on every tensor state, by the original matter tensor form and the rotated ghost antighost transpose."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-relative-isotropic"),
                DeclarationHandle.Create(Prefix + "relative_isotropic"), H("The relative kernel is isotropic for F"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If B0 kills both inputs, their uninserted F pairing is zero. The actual CAR gives left=B0(C0 left); the proved B0 transpose then places B0 on the right input. This is isotropy of the uninserted form, not degeneracy or positivity of the C0-inserted physical form."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-relative-pi"),
                DeclarationHandle.Create(Prefix + "Pi_relative"), H("Parity preserves the relative kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pi anticommutes with B0, so a relative vector remains relative after applying Pi."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-relative-v-zero"),
                DeclarationHandle.Create(Prefix + "V0_relative"), H("The actual obstruction operator preserves relativity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("V0 is the original statewise finite sum of 2n times C(-n)C(n). At n=0 its coefficient vanishes. At every nonzero n the CAR anticommutes B0 through both C factors; each weighted summand preserves ker B0, and so does their actual finsum. No universal vanishing of V0 is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-relative-left-obstruction"),
                DeclarationHandle.Create(Prefix + "left_boundary_obstruction"), H("Left boundary obstruction with its positive sign"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Q-cycle y and arbitrary ambient u, F(Q u,C0 y)=one-half F(Pi u,V0 y). The sign is positive: the negative original-Q transpose combines with the negative actual anticommutator {Q,C0}=-V0/2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-relative-right-obstruction"),
                DeclarationHandle.Create(Prefix + "right_boundary_obstruction"), H("Right boundary obstruction with its negative sign"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Q-cycle x and arbitrary ambient u, F(x,C0 Q u)=-one-half F(x,V0 u). The other term is F(x,Q C0 u), which vanishes by the actual cycle-boundary orthogonality with an unrestricted ambient preimage."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-relative-two-boundary-slots"),
                DeclarationHandle.Create(Prefix + "boundary_pairing_vanishes"), H("Both inserted boundary pairings vanish for relative preimages"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If u is relative and y is a relative Q-cycle, F(Q u,C0 y)=0 and F(y,C0 Q u)=0 simultaneously. Pi u, V0 y and V0 u are relative by the preceding actual operator laws, so uninserted relative isotropy kills both obstruction pairings. The preimage must be relative: these identities do not establish C0 descent on the entire original absolute cohomology."))), DescribeRole.Theorem))));
}

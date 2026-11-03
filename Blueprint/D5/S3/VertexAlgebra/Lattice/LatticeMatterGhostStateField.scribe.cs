using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeMatterGhostStateFieldDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original all-state matter and ghost fields have locally finite tensor coefficients and signed locality.",
        H("The Original All-State Matter/Ghost Field"),
        Blocks(
            Paragraph(Text("The carrier is the original algebraic LatticeMatterGhostCoupling.State D: "
                + "the finite-charge lattice polynomial carrier tensor CountableOccupationFock.Fock over C. "
                + "The construction uses the original LatticeAllStateField.Y and BcGhostStateField.Y. "
                + "Normalized mode n is raw Laurent power -n-1. No endomorphism family is assumed globally finite.")),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-tensor-coefficients"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.tensor_coefficients"),
                H("The literal locally finite tensor coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For any D, matter states u,v, ghost states a,b, integer n and actual tail bounds M,G, the coefficient is the finsum over k of Ym(u)[[k]]v tensor Yg(a)[[n-1-k]]b. Its support lies in n-G <= k <= M-1 and n >= M+G kills it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-statefield-truncation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_truncation"),
                H("All original algebraic states and inputs truncate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every original tensor field state s and original algebraic input x, one integer N kills every normalized mode n >= N. The construction descends through both tensor relations using pointwise finite support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-statefield-vacuum-creation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_vacuum_creation"),
                H("The original vacuum and all-state creation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Y(vacuum) is the identity field, mode -1 on the vacuum creates every state, every nonnegative vacuum coefficient vanishes, and the original tensor translation kills the vacuum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-statefield-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_covariance"),
                H("The actual translation acts on every coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The tensor sum of original matter translation and original ghost L(-1) has commutator with mode n equal to -n times mode n-1, for every original field state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-statefield-parity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_parity"),
                H("Original ghost parity acts on the full field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Identity on matter tensor the actual occupation parity intertwines every coefficient with the coefficient of the parity-transformed field state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-conformal-modes"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.conformal_modes"),
                H("The genuine coupled conformal state has the actual modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite rank including zero, arbitrary complex matrix H and integer m, the coefficient m+1 of omega_m tensor vac_g plus vac_m tensor Omega_g is matterMode(D,H,m) + ghostVirasoro(D,m). No inverse-Gram or rank-26 assumption occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-current-zero-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.current_zero_mode"),
                H("The literal coupled current has the original total charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every D and arbitrary complex H, mode zero of omega_m tensor ket{1} plus vac_m tensor Jg equals LatticeBRST.totalCharge(D,H). The exact integer reindex m=k-1 identifies the original matter coupling T, and the ghost term is the original anomalous Qg."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghoststatefield-statefield-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_locality"),
                H("Signed locality has an actual finite-support proof"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For arbitrary algebraic homogeneous field states of parities p,q, one order N kills their signed discrepancy under delta(p,q)=f(p+1,q)-f(p,q+1). Only same-order pair families are summed before clearing the two factor polynomials. The cleared factors have rectangular support, so finite convolution permits substitution of both locality identities. Mixed-order infinite-support rays remain allowed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The vacuum cuts are original: b_p creates exactly for p <= -2 and c_q creates "
                + "exactly for q <= 1. The b-state mode n is b(n-1), and the c-state mode n is c(n+2). "
                + "Finite tail intervals and genuine tensor induction supply all-state bilinearity.")),
            Paragraph(Text("Classical attribution: Bakalov-Kac, math/0402315v1 section 4.1; "
                + "Matsuo-Nagatomo, hep-th/9706118v1. The imported coefficient kernels retain Scott Carnahan, "
                + "vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache-2.0. "
                + "Sugawara architecture retains Kalle Kytola, VirasoroProject revision "
                + "5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Apache-2.0. No literature novelty is asserted.")),
            Paragraph(Text("The field and current identities include degenerate lattices and rank zero. "
                + "They impose no inverse-Gram or rank-26 hypothesis. The accepted total-charge square anomaly "
                + "remains in LatticeBRSTSquare; pure ghost Qg is anomalous. The total-Q field derivation "
                + "is proved in LatticeMatterGhostBRSTDerivation. This module does not prove coupled "
                + "three-index Jacobi, no-ghost, full string theory or AdS/CFT.")))));
}

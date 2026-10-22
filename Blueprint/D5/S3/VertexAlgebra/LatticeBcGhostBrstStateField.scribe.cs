using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostBrstStateFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostBrstStateField.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original BRST current is the actual tensor state-field of its original candidate state; "
            + "its zero mode is the original charge and acts as a signed derivation.",
        H("Original BRST State, Field, and Charge"),
        Blocks(
            Paragraph(Text("The carrier is the full algebraic lattice Carrier(D) tensor over Complex "
                + "with the original bc Fock(Complex). D is arbitrary, including rank zero, and H is "
                + "an arbitrary complex matrix of its rank. No inverse-Gram, symmetry, rank 26, "
                + "cutoff, analytic completion, or nilpotence assumption is used here. The accepted "
                + "tensor map is named stateField, not Y, in its source.")),
            Describe.Lean(
                DescribeId.Create("brst-candidate-field"),
                DeclarationHandle.Create(Prefix + "candidate_field"),
                H("The unchanged candidate has the actual original current as its field"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The candidate is the original matter conformal state tensor "
                    + "c(1)vacuum, plus one half of the matter vacuum tensor the minus-one mode of "
                    + "Y(c(1)vacuum) applied to the original ghost omegaState. Its ghost factor uses "
                    + "BcGhostSuperResidues.stateField_residue_closure with parities 1 and 0 and "
                    + "parameter minus one. The resulting Koszul sign is plus one. Actual tensor "
                    + "bilinearity and the actual matter vacuum field identify the independently "
                    + "constructed current. This is a consumed bind-only integration, not new "
                    + "mathematical content attributed to supplier transport."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("brst-candidate-zero"),
                DeclarationHandle.Create(Prefix + "candidate_zero"),
                H("The actual tensor zero mode is the exact original Q"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The field identification consumes the existing unrestricted "
                    + "LatticeBcGhostBrstCurrent.current_zero. Physical ghost coefficients remain "
                    + "c(index+2), and the original ghost normal split remains at physical index "
                    + "minus one. Every support is finite on each vector; no globally finite sum of "
                    + "endomorphisms is asserted. This consumed bind-only identity is used by the "
                    + "actual original-Q derivation proof."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("brst-candidate-parity"),
                DeclarationHandle.Create(Prefix + "candidate_mem"),
                H("The original candidate is odd"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original c-state is the singleton odd ghost state; the "
                    + "original ghost conformal state consists of two even two-site states. Actual "
                    + "ghost mode parity and actual tensor parity prove that the unchanged candidate "
                    + "lies in homogeneous 1. This consumed parity bridge provides actual signed "
                    + "locality for the derivation, rather than assuming current parity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("brst-current-parity"),
                DeclarationHandle.Create(Prefix + "current_mem"),
                H("Every original current mode is odd"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every mode of the actual current sends tensor parity p to "
                    + "parity 1+p. The proof uses the field identification and actual tensor mode "
                    + "parity; Q_mem consumes this bind-only bridge."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("brst-charge-parity"),
                DeclarationHandle.Create(Prefix + "Q_mem"),
                H("The exact original Q is odd"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Q sends homogeneous p to homogeneous 1+p on the full "
                    + "original carrier. The relative-locality step for the actual field Y(Qa) "
                    + "consumes this bridge. The existing unrestricted Q_vacuum in "
                    + "LatticeBcGhostBrstCurrent already proves that Q kills the actual tensor "
                    + "vacuum; it is reused, not redeclared."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("brst-signed-derivation"),
                DeclarationHandle.Create(Prefix + "Q_derivation"),
                H("Actual signed zero-mode derivation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every homogeneous a of parity p, every integer n, and "
                    + "every algebraic vector v, Q(Y(a)_n v)=Y(Qa)_n v+(-1)^p Y(a)_n Qv. The "
                    + "proof constructs the actual signed zero residue, proves its relative Dong "
                    + "locality on the tensor carrier, and applies actual vacuum uniqueness with "
                    + "creation and translation covariance. It assumes neither this conclusion "
                    + "nor full tensor Jacobi. The consumed zero-residue locality proof adapts the "
                    + "sealed BcGhostSuperResidues.nonnegative_residue_locality polynomial-shift "
                    + "proof to a general complex module at residue degree zero. This is explicit "
                    + "source attribution, not a claim of a new Dong theorem or of independent "
                    + "mathematical novelty."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("brst-mixed-derivation"),
                DeclarationHandle.Create(Prefix + "Q_derivation_mixed"),
                H("Arbitrary mixed tensor states"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The arbitrary state law uses its actual even and odd "
                    + "projections: Q(Y(a)_n v)=Y(Qa)_n v+Y(a_even)_n Qv-Y(a_odd)_n Qv. No "
                    + "homogeneity restriction is placed on a or v in this endpoint."))),
                DescribeRole.Theorem),
            Paragraph(Text("Only the actual zero residue needed by Q is closed here. The full "
                + "all-integer tensor residue and Borcherds/Jacobi identities remain open; the "
                + "supplier BorcherdsEquation is only a definition. The original nilpotence "
                + "theorem retains both equations H*gramComplex(D)=1 and gramComplex(D)*H=1 "
                + "and the critical rank equation D.rank=26. No cohomology VOA descent, complete "
                + "string theory, AdS/CFT, or emergent spacetime conclusion is asserted. Native "
                + "issue 15040 and escape registration remain unfinished; no registration or "
                + "independent review is claimed.")))));
}

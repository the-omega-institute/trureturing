using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeThetaCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeThetaCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite-charge restrictions of the all-charge Sugawara zero mode.",
        H("Actual Lattice Theta Character"),
        Blocks(
            Definition("cutoff-coeff-equiv", "cutoffCoeffEquiv", "Finite cutoff coefficient equivalence",
                "The charge-supported actual Sugawara eigenspace is identified with finitely supported coefficients on the literal charge and energy cutoff. The original H, H*gramComplex D = 1, and gramComplex D*H = 1 hypotheses are retained."),
            Theorem("cutoff-index-finite", "cutoffIndex_finite", "Finite fixed-charge energy fibres",
                "For every finite charge set and every signed integer energy, the literal cutoff index is finite by oscillatorLeFinite and a dependent finite charge sum."),
            Theorem("cutoff-grade-finite", "cutoffActualGrade_finiteDimensional", "Finite actual cutoff eigenspaces",
                "The actual charge-supported Sugawara eigenspace is finite-dimensional through its actual coefficient basis. This does not invoke a trace on an infinite full grade."),
            Definition("theta-restriction", "thetaRestriction", "Actual reflected restriction",
                "For a symmetric finite charge set, thetaLinear is restricted to the actual charge-supported Sugawara eigenspace. The restriction is built by codRestrict and domRestrict from the actual operator."),
            Theorem("cutoff-theta-trace-neutral-sum", "cutoff_theta_trace_neutral_sum", "Finite actual theta trace",
                "The finite matrix trace of the actual restricted theta operator is the signed occupation sum over the neutral charge labels. Reflection is applied before diagonal cancellation, and no infinite-grade or scalar proxy trace is used."),
            Theorem("actual-trace-series", "actual_theta_trace_series", "Actual trace series",
                "The neutral actual traces are grouped by integer oscillator energy. The signed occupation majorant gives absolute summability and a HasSum for the actual coefficient series, including the zero-rank case and complex phases."),
            Theorem("actual-eta-character", "actual_theta_character_eta", "Eta value of the actual trace character",
                "The ordinary vacuum shift is minus rank/24. Absolute convergence and the grouped occupation HasSum identify the normalized literal neutral Sugawara traces with (eta(tau)/eta(2 tau))^rank on the upper half-plane."),
            Theorem("actual-s-interchange", "actual_theta_character_S", "Modular S and identity-ground interchange",
                "The actual reflecting character at -1/tau equals 2^(rank/2) times (eta(tau)/eta(tau/2))^rank. The principal-root identity follows from the logarithm branch on the upper half-plane and positive real scaling. If the integral Gram determinant is a unit, symplectic coordinates make the rank even and the actual ground dimension is 2^(rank/2). The accepted half-Fock character with identity ground insertion and this actual ordinary trace character interchange under S. The half-Fock ground shift rank/16 and central charge rank give its vacuum exponent rank/48."),
            Theorem("positive-full-grade", "positive_full_grade_eq_cutoff", "Full positive-definite Sugawara eigenspace",
                "Positive real Gram form bounds the charge ellipsoid. Every label in the full signed-energy Sugawara kernel lies in the finite charge ellipsoid and finite oscillator sublevel. Its literal kernel equals the finite charge cutoff, with both original inverse Gram equations retained."),
            Theorem("positive-full-character", "positive_full_theta_character", "Literal full-grade trace and character",
                "Theta is restricted from the original carrier to the full Sugawara kernel. Positive definiteness supplies finiteness before its trace is taken. The full trace at a negative energy is zero and at nonnegative energy is the signed integer coefficient. Its series is absolutely summable for norm q less than one, including q zero. The normalized full trace series has the same eta value and modular S law as the neutral actual character."),
            Theorem("symmetric-cutoff-limit", "symmetric_charge_cutoff_limit", "Cofinal symmetric-charge regularization",
                "Symmetrizing arbitrary finite charge sets gives a directed cofinal exhaustion. For every signed energy, the actual finite cutoff traces stabilize exactly when zero is included. The normalized cutoff characters likewise stabilize to the actual neutral trace character. This is an explicit regularized limit for indefinite Gram forms; it is never a trace on an infinite full grade."),
            Paragraph(Text("The insertion in the S interchange is the identity on the actual ground module. Arbitrary ground insertions, parity-S and full modular-group laws, module identities, fusion and sewing require further proofs. The reflecting trace is distinct from the ordinary uninserted full-charge Gaussian theta series.")))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}

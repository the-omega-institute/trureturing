using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondPowersStormerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constant-one trace-norm inequality holds on every complex Hilbert space. It controls the trace-class terms in a covariance perturbation before and after bounded congruence.",
        H("Powers–Størmer and trace-class stability of square roots"),
        Blocks(
            Entry("compact-root", "isCompactOperator_sqrt_sub_of_isCompactOperator_sub",
                "Compact square-root difference",
                "Uniform real polynomial approximation on a common spectral interval gives operator-norm convergence. Each polynomial difference lies in the compact ideal by telescoping the differences of powers."),
            Entry("stormer-hs", "powers_stormer_isHilbertSchmidt",
                "Hilbert–Schmidt root difference",
                "In the real eigenbasis of the compact self-adjoint root difference, each squared eigenvalue is bounded by the modulus of the corresponding diagonal entry of the covariance difference."),
            Entry("stormer-bound", "powers_stormer_hsSq_le",
                "Powers–Størmer inequality",
                "Sum the diagonal bound in the eigenbasis and use the trace-norm bound for the diagonal pairing with the identity."),
            Entry("stormer-sharp", "powers_stormer_sharp",
                "Equality on the complex line",
                "The positive operators zero and identity on the complex line have a squared Hilbert–Schmidt root difference and a trace-norm difference both equal to one."),
            Entry("trace-add", "quarterPower_add_traceClass_sqrt_hs",
                "Trace-class correction to the quarter-power bound",
                "Add the absolute value of the self-adjoint correction to the reference, and its absolute value minus itself to the target. Both shifts are positive trace class. The squared estimate is three times the sum of the squared Hilbert–Schmidt factor and three times the trace norm of the correction."),
            Entry("trace-congruence", "quarterPower_add_traceClass_congruence_sqrt_hs",
                "Bounded congruence of the perturbation",
                "The congruence may act between different Hilbert spaces. Its squared operator norm multiplies the bound."),
            Entry("converse", "not_hs_sqrt_diff_of_add_traceClass_not_hs",
                "Persistence of the normalized converse",
                "For a corrected positive covariance, the root difference between it and the uncorrected positive covariance is Hilbert–Schmidt in the same normalizing congruence. Subtraction reduces a hypothetical Hilbert–Schmidt difference to the uncorrected converse."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}

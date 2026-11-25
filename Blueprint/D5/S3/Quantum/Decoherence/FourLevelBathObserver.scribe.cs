using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FourLevelBathObserverDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/FourLevelBathObserver.";
    private static readonly LibraryNoteRef ThermalOperations =
        LibraryNoteRef.Create("D5/L/Resource/vomende2022thermaloperations");
    private static readonly LibraryNoteRef Masking =
        LibraryNoteRef.Create("D5/L/HilbertOperators/dinghu2020masking");
    private static readonly LibraryNoteRef Wheeler =
        LibraryNoteRef.Create("D5/L/Observer/wheeler1999informationphysics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual conditional records of a purified Gibbs bath hide a basis label in each margin and reveal it jointly.",
        H("Reading the purified bath record"),
        Blocks(
            Paragraph(Text(
                "Preparation supplies the coherent state Σᵦ √p(b) |b,b⟩ on bath B and reference R, "
                + "initially independent of the qutrit. Its B marginal is the same Gibbs state used "
                + "in the fixed-bath channel. The interaction is U on S and B tensored with the "
                + "identity on R. Energy conservation is the commutation condition on U.")),
            Paragraph(Text(
                "Access to R and phase-sensitive measurements are separate assumptions of the readout. "
                + "Wheeler's It from Bit supplies historical context for the question “Is the label j?” "
                + "Ding and Hu give the fixed-modulus masking context. Here the label runs over the three "
                + "prescribed qutrit basis inputs.")),
            Theorem("purified-bath-marginals", "purifiedBath_marginals", "Both preparation marginals",
                "For a normalized nonnegative law p, the coherent preparation has marginal diag(p) "
                + "on both factors."),
            Theorem("purified-output-density", "purifiedOutput_density", "The actual output is a density",
                "A unitary on S and B, lifted by the identity on R, preserves positivity and unit "
                + "trace for every density input with the normalized preparation."),
            Theorem("purified-output-entry", "purifiedOutput_entry", "Entries of the physical output",
                "For any system matrix X, its (i,j) entry multiplies the outer product of the two "
                + "corresponding record vectors. The record for i has amplitudes √p(b) z(b,i) at |b,b⟩."),
            Theorem("conditional-record", "conditionalRecord_eq", "The conditional record from the output",
                "Taking the system partial trace after basis input i gives the rank-one record density "
                + "on bath and reference."),
            Theorem("conditional-record-marginals", "conditionalRecord_marginals", "The marginal records",
                "For nonnegative p and unit phases, either partial trace of the basis-conditioned "
                + "record is diag(p), independent of the label.", Masking),
            Theorem("joint-basis-born", "joint_basis_born", "The joint coordinate readout",
                "The probability of coordinates (b,r) is p(b) when b = r and zero otherwise, for "
                + "every input label.", Masking),
            Theorem("diagonal-observable-expectation", "diagonal_observable_expectation",
                "Expectations for diagonal observables",
                "For any diagonal observable in the joint coordinate basis, the expectation is "
                + "its average over (b,b) with weights p(b)."),
            Theorem("orthogonal-readout-projection", "orthogonalReadout_projection",
                "Projective effects from an isometry",
                "The column projectors and the projector onto their orthogonal complement are "
                + "self-adjoint projections."),
            Theorem("orthogonal-readout-complete", "orthogonalReadout_complete",
                "The effects sum to the identity",
                "The column outer products sum to VVᴴ and the remaining effect is I − VVᴴ."),
            Theorem("orthogonal-readout-born", "orthogonalReadout_born",
                "Born law of the column readout",
                "On a column of an isometry, the matching effect has probability one and all "
                + "other effects have probability zero."),
            Theorem("joint-decoder-born", "joint_decoder_born", "An exact yes-or-no question for each label",
                "Under the weighted Gram identity, use the projector onto record j as the yes effect "
                + "and its complement as the no effect. The yes probability on actual record i "
                + "is one exactly when i = j. The complete label measurement also has a complementary "
                + "outcome with probability zero.", Wheeler, Masking),
            Theorem("fixed-bath-observable-bridge", "fixed_bath_observable_bridge",
                "One interaction for pinching and observation",
                "At any feasible fixed Gibbs law, one permitted phase unitary gives mixed-bath "
                + "pinching on every qutrit matrix. With the separate coherent preparation it also "
                + "supplies the actual records, their marginals and a projective decoder.", ThermalOperations),
            Theorem("feasible-gibbs-observer", "feasible_gibbs_observer", "A feasible Gibbs example",
                "For every β > 0, the energies matching (29, 27, 25, 19)/100 give the same bridge.",
                ThermalOperations))));

    private static DocumentBlock.Describe Theorem(
        string id, string name, string title, string statement, params LibraryNoteRef[] sources) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(sources),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}

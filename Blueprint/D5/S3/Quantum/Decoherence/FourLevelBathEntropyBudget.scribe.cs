using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FourLevelBathEntropyBudgetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget.";
    private static readonly LibraryNoteRef Coherence =
        LibraryNoteRef.Create("D5/L/Quantum/baumgratz2014coherence");
    private static readonly LibraryNoteRef Balance =
        LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved");
    private static readonly LibraryNoteRef EntropicIdentities =
        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities");
    private static readonly LibraryNoteRef ThermalOperations =
        LibraryNoteRef.Create("D5/L/Resource/vomende2022thermaloperations");
    private static readonly LibraryNoteRef Distinguishability =
        LibraryNoteRef.Create("D5/L/HilbertOperators/korzekwaetal2019distinguishing");
    private static readonly LibraryNoteRef OrderFourMethod =
        LibraryNoteRef.Create("D5/L/FiniteGroups/rajchelgasiorowskizyczkowski2018robust");
    private static readonly LibraryNoteRef Masking =
        LibraryNoteRef.Create("D5/L/HilbertOperators/dinghu2020masking");
    private static readonly LibraryNoteRef Wheeler =
        LibraryNoteRef.Create("D5/L/Observer/wheeler1999informationphysics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact marginal entropies and information for an arbitrary qutrit coupled to a purified Gibbs bath.",
        H("Entropy budgets of the purified four-level Gibbs bath"),
        Blocks(
            Paragraph(Text(
                "Fix a qutrit S with zero Hamiltonian, a four-level bath B with distinct energies E, "
                + "and a finite real inverse temperature β. The Gibbs weight p(b) is exp(−βE(b)) "
                + "divided by the sum of those exponentials over the four bath levels. "
                + "Prepare B and a four-level reference R coherently in Σᵦ √p(b) |b,b⟩, independently "
                + "of the input density ρ on S. Act with the phase unitary on SB and the identity "
                + "on R. Its phases have unit modulus and the p-weighted columns are orthonormal. "
                + "Energy conservation is imposed on SB with Hamiltonians 0 and E.")),
            Paragraph(Text(
                "The input ρ may be any positive semidefinite trace-one qutrit, including singular "
                + "and coherent inputs. Write aᵢ = ρᵢᵢ, Δρ for coordinate pinching, H for Shannon "
                + "entropy and S(·) for von Neumann entropy. Both entropies are in nats and use "
                + "the zero-weight convention.")),
            Theorem("gibbs-phase-budgets", "gibbs_phase_budgets", "Information in the actual evolved state",
                "The same energy-conserving phase interaction gives the budget for every density ρ. "
                + "The S marginal is Δρ. Both B and R have density diag(p). The SB marginal is "
                + "the evolved mixed-bath product state, and SR equals SB in the corresponding "
                + "coordinates. The BR marginal is the orthogonal pure-record mixture with weights a. "
                + "The S and BR entropies are H(a), the B and R entropies are H(p), the SB and SR "
                + "entropies are S(ρ) + H(p), and the SBR entropy is S(ρ). "
                + "The S:BR mutual information equals that of the coherent copy of ρ.",
                EntropicIdentities, Coherence, Balance, ThermalOperations),
            new DocumentBlock.DisplayFormula(Disp(Seq(
                Information("S", "B"), Sp, Eq, Sp, Information("S", "R"), Sp, Eq, Sp,
                Entropy("H", F.Id("a")), Sp, Minus, Sp, Entropy("S", Rho)))),
            new DocumentBlock.DisplayFormula(Disp(Seq(
                Information("S", "BR"), Sp, Eq, Sp, D(2), Sp, Entropy("H", F.Id("a")),
                Sp, Minus, Sp, Entropy("S", Rho), Comma, Quad, Sp,
                F.Id("I"), Open, F.Id("S"), Colon, F.Id("R"), Mid, Sp, F.Id("B"), Close,
                Sp, Eq, Sp, Entropy("H", F.Id("a"))))),
            Paragraph(Text(
                "Baumgratz, Cramer and Plenio identify H(a) − S(ρ) with the relative entropy "
                + "of coherence in the chosen basis. For the reduced SB evolution, the "
                + "Reeb–Wolf balance starts from ρ ⊗ diag(p). The returning Gibbs bath has "
                + "zero mean-energy change and zero relative entropy to its initial state, "
                + "so the balance gives I(S:B) equal to the system entropy gain.")),
            Theorem("populations-nonnegative", "populations_nonneg", "Nonnegative Born weights",
                "Each coordinate population of a positive semidefinite input density is nonnegative."),
            Theorem("populations-normalized", "sum_populations", "Normalized Born weights",
                "The populations sum to one by the trace of the input density."),
            Theorem("pinching-matrix", "pinching_matrix", "Pinching in the coordinate basis",
                "The pinched input matrix is diagonal with the Born populations on its diagonal."),
            Theorem("bath-state-matrix", "bathState_matrix", "Density of the original bath",
                "For any normalized nonnegative bath law p, the B marginal of the coherent "
                + "preparation has matrix diag(p)."),
            Theorem("output-state-matrix", "outputState_matrix", "Density of the evolved preparation",
                "The density-state conjugation of the independent preparation by the lifted "
                + "joint unitary has the actual purified-output matrix."),
            Theorem("sb-entry", "systemBathMarginal_entry", "Entries after tracing out the reference",
                "Sum the joint matrix entries over the common reference index to obtain each SB entry."),
            Theorem("sr-entry", "systemReferenceMarginal_entry", "Entries after tracing out the bath",
                "Sum the joint matrix entries over the common bath index to obtain each SR entry."),
            Theorem("purified-output-isometric-copy", "purifiedOutput_isometricCopy",
                "The coherent copy embedded in the actual record",
                "Under the weighted Gram identity, V = I ⊗ recordEmbedding is an isometry. "
                + "For every qutrit matrix X the actual phase output is V copyMatrix(X) V†. "
                + "Each off-diagonal input entry remains in the joint state.",
                EntropicIdentities, Masking),
            Theorem("system-marginals", "system_marginals", "The SB and SR densities",
                "For nonnegative normalized p and a unitary phase interaction, tracing out R "
                + "gives the mixed-bath evolution and tracing out B gives the same density in "
                + "the matching coordinates."),
            Theorem("record-marginal", "record_marginal", "The Born mixture on BR",
                "For the normalized preparation and orthonormal record columns, the BR "
                + "density is the mixture of the actual pure record densities with probabilities a."),
            Theorem("record-marginal-embedding", "record_marginal_embedding",
                "The pinched input embedded on BR",
                "The BR marginal is the rectangular record isometry applied to Δρ in the "
                + "original BR coordinates."),
            Theorem("gibbs-cubic-budgets", "gibbs_cubic_budgets", "One interaction for a fixed feasible law",
                "For the fixed Gibbs law, assume p(b) ≤ 1/3 for each b and a root 0 < t ≤ 1 "
                + "of the phase cubic with q(p,b)² t ≥ d(p,b)² at every b. There is one phase "
                + "interaction, chosen before the input, that conserves SB energy, pinches "
                + "every qutrit matrix in the mixed-bath channel, supplies a basis observation, "
                + "and realizes the purified budgets for every qutrit density.",
                Distinguishability, OrderFourMethod, ThermalOperations),
            Paragraph(Text(
                "For classical readout, measure S after the interaction in the input coordinate basis, keeping its "
                + "outcome X with law a. Conditional on each label of positive probability, "
                + "the bath and reference carry the corresponding pure phase record. The joint "
                + "decoder grants access to B and R and phase-sensitive projectors. The one-way "
                + "decoder grants a four-point Fourier measurement on R, a classical message "
                + "carrying its outcome k, and the matching phase-sensitive measurement on B.")),
            Theorem("basis-label-budgets", "basis_label_budgets", "Information of the measured label",
                "For any normalized nonnegative bath law with unit-modulus phases and orthonormal weighted "
                + "columns, the joint record determines X for any Born prior a, including priors with zero weights. "
                + "Each local label state has zero quantum mutual information.",
                Masking, Wheeler),
            new DocumentBlock.DisplayFormula(Disp(Seq(
                Information("X", "B"), Sp, Eq, Sp, Information("X", "R"), Sp, Eq, Sp, D(0), Comma, Quad, Sp,
                Information("X", "BR"), Sp, Eq, Sp, Entropy("H", F.Id("a"))))),
            Theorem("basis-readout-comparison", "basis_readout_comparison", "Readout of the phase record",
                "For each basis label, both local densities equal diag(p), and a joint coordinate measurement "
                + "has probability p(b) at (b,b) and zero off those pairs. "
                + "A joint record projector identifies the label with certainty. "
                + "Each Fourier outcome k has probability 1/4, and the joint law of k and the "
                + "bath decoder assigns 1/4 to the matching label and zero to every other answer. "
                + "Wheeler's apparatus question “Was the label j?” provides historical context.",
                Masking, Wheeler))));

    private static DocumentBlock.Describe Theorem(
        string id, string name, string title, string statement, params LibraryNoteRef[] sources) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(sources),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    private static Formula Information(string left, string right) =>
        Seq(F.Id("I"), Open, F.Id(left), Colon, F.Id(right), Close);

    private static Formula Entropy(string name, Formula argument) =>
        Seq(F.Id(name), Open, argument, Close);
}

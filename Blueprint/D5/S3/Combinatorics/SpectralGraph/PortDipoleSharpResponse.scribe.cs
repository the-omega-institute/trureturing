using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class PortDipoleSharpResponseDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.";
    private static readonly LibraryNoteRef Kron =
        LibraryNoteRef.Create("D5/L/GraphInvariants/dorflerbullo2013kron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp zero-shift response of a unit dipole with two prescribed moments on finite connected conductance graphs.",
        H("Sharp dipole response at two prescribed moments"),
        Blocks(
            Paragraph(Text(
                "A real symmetric matrix L with zero row sums and nonpositive off-diagonal entries "
                + "is the conductance Laplacian. Edge ij is present when −Lᵢⱼ > 0. "
                + "With d = eᵢ − eⱼ and distinct terminals, the exact moments are p = dᵀLd/2 "
                + "and q = ‖Ld‖²/2. Unit current solves Lu = d, so the effective resistance "
                + "is uᵢ − uⱼ and the normalized dipole response is (uᵢ − uⱼ)/2. "
                + "Dörfler and Bullo supply the electrical-network model. The moment-constrained "
                + "proof here derives two energy bounds and an exact-moment family approaching their maximum.")),
            Entry("current-solution", "exists_current_solution", "Unit current on connected support",
                "On any finite carrier with connected positive-conductance support, every terminal pair i, j "
                + "admits a solution of Lu = d. For f = d/√2, every w satisfying Lw = f has "
                + "fᵀw = (uᵢ − uⱼ)/2. The energy identity and connectedness force the kernel to consist "
                + "of constants, so the zero-sum dipole belongs to the range. This theorem also allows i = j.",
                AssessedProvenance.FromRepo(Kron)),
            Entry("response-lower-bound", "response_lower_bound", "Two-moment lower bound on any finite carrier",
                "For distinct terminals and a unit-current solution, assume the two moment equalities, "
                + "p > 0 and q < 4p². The normalized response is at least B = max{1/p, 2p/(4p² − q)}, "
                + "and is strictly larger when q > p². The proof tests the electrical energy first with "
                + "the dipole and then with a vector supported on the two terminals and weighted by their "
                + "Laplacian entries. The equality conditions give strictness.",
                AssessedProvenance.FromRepo()),
            Entry("sharp-infimum", "isGLB_responses", "Sharp infimum over connected conductance graphs",
                "For p > 0 and p² ≤ q < 4p², B is the greatest lower bound of normalized responses "
                + "over all finite connected positive-conductance supports with distinct terminals and both "
                + "moments prescribed exactly. The resistance infimum is 2B. At q = p² a single edge "
                + "of conductance p/2 realizes B. For q > p² a four-vertex graph has a three-edge path "
                + "with conductances x, M, y and an optional direct terminal edge of conductance t. "
                + "The moment identities are independent of M. With x and y positive and t ≥ 0 chosen "
                + "for the prescribed p and q, the normalized response approaches B as M grows.",
                AssessedProvenance.FromRepo()),
            Entry("infimum-attainment", "infimum_mem_responses_iff", "Attainment at zero variance",
                "Under the same moment hypotheses, B belongs to the set of normalized responses "
                + "exactly when q = p². Equivalently, the resistance infimum is attained precisely "
                + "at zero dipole variance. The single-edge realization gives attainment at the endpoint, "
                + "and the strict lower bound rules it out at positive variance.",
                AssessedProvenance.FromRepo()))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}

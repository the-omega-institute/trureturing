using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FourLevelBathCubicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/FourLevelBathCubic.";
    private static readonly LibraryNoteRef ThermalOperations =
        LibraryNoteRef.Create("D5/L/Resource/vomende2022thermaloperations");
    private static readonly LibraryNoteRef Distinguishability =
        LibraryNoteRef.Create("D5/L/HilbertOperators/korzekwaetal2019distinguishing");
    private static readonly LibraryNoteRef HaagerupMethod =
        LibraryNoteRef.Create("D5/L/FiniteGroups/rajchelgasiorowskizyczkowski2018robust");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact fixed-bath pinching criterion and two Gibbs laws below the one-third cap.",
        H("A guarded cubic for exact fixed-bath pinching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-bath-pinching-iff-cubic"),
                DeclarationHandle.Create(Module + "fixed_bath_pinching_iff_cubic"),
                H("The scalar criterion at the prescribed Gibbs law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ThermalOperations, Distinguishability, HaagerupMethod),
                Blocks(
                    Paragraph(Text(
                        "At fixed injective E and finite real β, write p for the Gibbs law. The operation "
                        + "exists exactly if every p(b) ≤ 1/3 and there is one 0 < t ≤ 1 satisfying "
                        + "(1 − 2p(b))²t ≥ (4p(b) − 1)² for all b and phaseCubic(p,t) = 0. "
                        + "The parameter t is the squared spectral gap of a real complementary frame.")),
                    Paragraph(Text(
                        "The scalar supplier uses the fixed-diagonal pure-state problem. Completing the "
                        + "three columns gives the repeated-column unistochastic slice [p,p,p,1−3p]. "
                        + "Korzekwa et al., Lemma 5, Eq. (19) and Appendix C.3, relate this slice to "
                        + "distinguishability and apply Haagerup's order-four test, described in "
                        + "Appendix A of Rajchel, Gąsiorowski and Życzkowski."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-fixed-bath-example"),
                DeclarationHandle.Create(Module + "feasible_fixed_bath_example"),
                H("An exact realization below the cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ThermalOperations, Distinguishability),
                Blocks(Paragraph(Text(
                    "For each β > 0 choose the distinct energies matching (29, 27, 25, 19)/100. "
                    + "The cubic changes sign between 1/2 and 1 with all guards satisfied on that interval. "
                    + "One energy-conserving unitary for that bath pinches all qutrit density inputs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("infeasible-fixed-bath-example"),
                DeclarationHandle.Create(Module + "infeasible_fixed_bath_example"),
                H("An obstruction strictly below the cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ThermalOperations, Distinguishability),
                Blocks(Paragraph(Text(
                    "For each β > 0 choose the distinct energies matching (19999, 15001, 12000, 13000)/60000. "
                    + "Every weight is strictly below 1/3 and the cubic is positive for every t > 0. "
                    + "At that fixed bath, every permitted unitary fails to pinch at least one density input."))),
                DescribeRole.Theorem))));
}

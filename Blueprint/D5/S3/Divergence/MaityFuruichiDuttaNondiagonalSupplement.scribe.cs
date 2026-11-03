using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class MaityFuruichiDuttaNondiagonalSupplementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common orthogonal change of basis makes both states nondiagonal while preserving the Tsallis ordering reversal.",
        H("Both states nondiagonal in the same basis"),
        Blocks(
            Paragraph(Text("This supplement answers Supriyo Dutta's question of 3 November 2026. "
                + "The mathematical note is by Haobo Ma and Wenlin Zhang, licensed CC BY 4.0. "
                + "It supplements the existing Maity-Furuichi-Dutta ordering refutation and does not resolve another conjecture. "
                + "Supriyo Dutta is distinct from Soumyojyoti Dutta and Tushar in other correspondence.")),
            Entry("orthogonal-matrix", "U", "The common change of basis",
                "U = (1/sqrt(2)) [[1,1],[1,-1]] is real, self-adjoint and orthogonal.", DescribeRole.Definition),
            Entry("first-state", "rhohat", "The first nondiagonal state",
                "rhohat = (1/10) [[5,3],[3,5]]. Both off-diagonal entries are 3/10.", DescribeRole.Definition),
            Entry("second-state", "sigmahat", "The second nondiagonal state",
                "sigmahat = (1/250) [[125+12 sqrt(6),-69],[-69,125-12 sqrt(6)]]. "
                + "Both off-diagonal entries are -69/250.", DescribeRole.Definition),
            Entry("invariance", "functions_unitary", "The three actual source functions are unitarily invariant",
                "The same unitary conjugates both arguments. Every real spectral function commutes with "
                + "this conjugation, and cyclicity preserves its trace. Consequently the existing renyiRZ, B2 "
                + "and tsallis definitions retain their values, for all parameters. On positive definite "
                + "states these functions use positive spectral calculus. The extension to arbitrary matrices "
                + "in the statement follows the total cfc convention, which is zero outside its predicate."),
            Entry("states", "matrix_facts", "Density, determinants, entries and noncommutation",
                "Both matrices are positive definite with trace one and determinant 4/25. The (0,1) entry "
                + "of their commutator is -18 sqrt(6)/625, which is nonzero. Thus they are noncommuting "
                + "density matrices with nonzero off-diagonal entries in this common basis."),
            Entry("eigenvalues", "characteristic_polynomials", "The two eigenvalues",
                "Each characteristic polynomial is (X-4/5)(X-1/5), so each state has eigenvalues "
                + "4/5 and 1/5, each with multiplicity one."),
            Entry("common-basis", "common_orthogonal_conjugation", "One orthogonal matrix conjugates the entire pair",
                "The original states are rho = diag(4/5,1/5) and sigma = (1/125) [[28,6 sqrt(6)],[6 sqrt(6),97]]. "
                + "The displayed rhohat and sigmahat equal U rho U* and U sigma U*. Every real spectral "
                + "function is covariant, including the powers and deformed logarithm occurring in all three "
                + "source functions. The commutator is conjugated by that same U. Nondiagonality depends "
                + "on the common basis; the bound values and noncommutation are invariant."),
            Entry("parameters", "parameter_conditions", "The source parameters are admissible",
                "At alpha = r = 1/2, z = 2 and q = 1, all five source conditions hold: "
                + "0 <= alpha, alpha < 1, r is nonzero, z > 0 and q > 1-alpha."),
            Entry("spectral-quantities", "spectral_quantities", "The spectral sandwiches",
                "The fidelity trace F for the nondiagonal pair is exactly (2117+288 sqrt(2))/3125. "
                + "The inverse-power sandwich is U A U*, where A = (1/25) [[7,3 sqrt(6)],[3 sqrt(6),97]] "
                + "is the original inverse-power sandwich. These identities transport the actual spectral "
                + "expressions used by the bounds."),
            Entry("values", "exact_values_and_bounds", "Exact values and the strict chain",
                "The old exact sandwich trace (2117+288 sqrt(2))/3125 gives "
                + "B1 = renyiRZ = 4(1-sqrt((2117+288 sqrt(2))/3125)). The existing positive square-root "
                + "calculation gives B2 = 2-20/sqrt(154). Transport by the common U gives "
                + "B2 < 2/5 < B1. The two-point functional calculus also gives the new exact value "
                + "D = tsallis(1/2,rhohat,sigmahat) = 48/125. Since 1250^2 < 154*101^2, D < B2 < B1. "
                + "Thus both individual upper bounds hold at this pair while their proposed relative order fails."),
            Entry("restricted-order", "claim", "The old ordering restricted to this nondiagonal setting",
                "This is the already refuted comparison B1 <= B2, restricted to positive definite "
                + "noncommuting qubit states with trace one and nonzero (0,1) entries in the same basis, "
                + "at the displayed source parameters. It introduces no new conjecture.", DescribeRole.Definition),
            Entry("refutation", "result", "The same reversal persists with both states nondiagonal",
                "The explicit states meet every hypothesis of the restricted comparison, and their strict "
                + "bound reversal contradicts its conclusion. This says nothing about other parameter choices "
                + "or the source's commuting comparison."))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProbabilityTransport;

internal sealed class HalfRangePotentialsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded rectangular costs admit half-range Lipschitz majorants of arbitrary feasible potentials.",
        H("Half-range potential regularization"), Blocks(
            Describe.Lean(
                DescribeId.Create("half-range-potential-majorants"),
                DeclarationHandle.Create("D5/S3/Geometry/ProbabilityTransport/HalfRangePotentials.exists_half_range_majorants"),
                H("Simultaneous feasibility, domination and exact Lipschitz bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let X and Y be arbitrary pseudometric spaces in independent universes. Let M be real, let L be nonnegative, and let c on X times Y take values between 0 and M and be L-Lipschitz for the maximum product metric. Let K and H be arbitrary nonempty subsets of X and Y. Suppose arbitrary real functions phi on K and psi on H satisfy phi(k) + psi(h) <= c(k,h) for every pair k,h. There exist a real shift a and globally defined L-Lipschitz functions F and G, both taking values in [-M/2,M/2], such that F(x) + G(y) <= c(x,y) everywhere, phi(k) + a <= F(k), and psi(h) - a <= G(h). Nonnegativity of M follows from the cost bounds and nonempty supports; it is not an additional hypothesis.")),
                    Paragraph(Text("Define f(x) as the infimum over h in H of c(x,h) - psi(h). Feasibility at one fixed point of K bounds each fiber below, so the real infima are meaningful without an attained minimum. The cost bounds imply f(x) <= f(z) + M, and fixing one point of H bounds f above. If b is the supremum of f, then b-M <= f(x) <= b. The common shift a = -b + M/2 therefore places F(x) = f(x)+a in the required half-range and preserves domination of phi.")),
                    Paragraph(Text("For each support index, the residual cost is L-Lipschitz. Comparing every residual at x with the corresponding residual at z, then passing to infima, gives f(x) <= f(z) + L dist(x,z). This proves the exact Lipschitz bound without continuity or boundedness assumptions on the original potentials. Applying the same comparison to g(y) = infimum over x in X of c(x,y)-F(x) gives an L-Lipschitz function bounded below by -M/2. Set G(y) = min(g(y),M/2). The upper clipping preserves Lipschitz regularity and global feasibility. The bound b <= M-psi(h) ensures that clipping also preserves psi(h)-a <= G(h).")),
                    Paragraph(Text("The construction is a classical double c-transform followed by recentering and clipping; c-transforms are discussed by Peyre and Cuturi, Computational Optimal Transport, arXiv:1803.00567v4, section 5.1. No originality of that construction is asserted. Compactness, completeness, finiteness, symmetry and a triangle inequality for the cost are unnecessary. The original potentials need no regularity. The feasibility hypothesis is every-pair feasibility on the support rectangle; a product-almost-everywhere inequality is not asserted to suffice.")),
                    Paragraph(Text("On compact metric spaces the Lipschitz functions are continuous, so this gives continuous bounded feasible majorants with the same shift. For probability measures concentrated on K and H, measurable integrable original potentials dominated on those supports have no larger dual integral sum: integrate the two inequalities and cancel the opposite shifts. This application still requires the stated every-pair feasibility and the relevant measurability and integrability assumptions; neither dual attainment nor arbitrary almost-everywhere regularization follows from the statement alone."))),
                DescribeRole.Theorem))));
}

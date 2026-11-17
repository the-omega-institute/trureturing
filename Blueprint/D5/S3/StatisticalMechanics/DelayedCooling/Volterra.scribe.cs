using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.DelayedCooling;

internal sealed class VolterraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/DelayedCooling/Volterra.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-Lebesgue integrated delay equation has a unique raw sample for every "
            + "locally integrable bath and implies regularity and separate bath integrability.",
        H("The raw integrated cooling equation"),
        Blocks(
            Paragraph(Text(
                "The source is the delayed Newton equation in Santos, The role of preparation "
                    + "protocols in the Mpemba effect under time-delayed Newton cooling, "
                    + "arXiv:2611.12328v1, Section 3 and Appendix. The delay, time and temperature "
                    + "are real. A sample has its own real preparation start a and equilibrium q. "
                    + "The bath is a raw real function. In particular, changing its value at a "
                    + "quench can change its pointwise supremum even though the Lebesgue integral "
                    + "does not see that single point. No quotient of bath histories is taken.")),
            Node("IntegratedSolution", "The finite-Lebesgue input equation",
                "The sample equals q at every time at most a. For each t at least a, the "
                    + "total forcing b(s) minus T(s-tau) is Lebesgue integrable from a to t, "
                    + "and T(t) is q plus that integral. The integrability clause specifies "
                    + "the meaning of the input integral. Continuity or absolute continuity "
                    + "of T and separate integrability of b are not assumed.", DescribeRole.Definition),
            Node("integrated_solution_bridge", "Pointwise uniqueness and derived regularity",
                "For every positive delay, the integrated equation forces continuity on the "
                    + "whole real line and absolute continuity on every finite interval from a. "
                    + "The bath itself is integrable on each such interval: add the continuous "
                    + "delayed sample to the integrable total forcing. At every t greater than a "
                    + "where the raw bath is continuous, T has derivative b(t) minus T(t-tau). "
                    + "Any two integrated solutions with the same a, q and raw bath agree "
                    + "pointwise on the whole real line. The uniqueness proof inducts over "
                    + "successive delay-length intervals. Every delayed argument in the next "
                    + "interval lies in the already equal past. This identifies actual sample "
                    + "values, including quench endpoints; it is stronger than AE equality.",
                DescribeRole.Theorem),
            Node("exists_unique_integrated_solution", "Existence by finite method of steps",
                "For every positive delay and every raw bath integrable on each finite "
                    + "interval after a, exactly one integrated sample exists. Start with "
                    + "the constant function q, and repeatedly integrate the bath minus "
                    + "the preceding approximation shifted by tau, retaining q before a. "
                    + "Every approximation is continuous. The m-th approximation agrees "
                    + "with the n-th one through a+n*tau whenever m is at least n. "
                    + "Choose at time t the approximation numbered floor((t-a)/tau)+1. "
                    + "Stabilization makes this a single raw solution with the required "
                    + "integrable forcing on every finite interval. No convergence "
                    + "hypothesis, small delay bound or assumed solution is used.", DescribeRole.Theorem),
            Paragraph(Text(
                "These statements cover the finite-Lebesgue integrated interpretation of "
                    + "the source equation. They do not identify every unspecified classical "
                    + "or quench solution convention with this integrated interpretation. "
                    + "Proper-Riemann inclusion remains a separate obligation. They impose no "
                    + "common preparation duration on a pair of samples. Monotone cooling, "
                    + "a strict unique crossover and the globally optimized balanced synchronous "
                    + "comparison remain obligations of the original whole event.")))));

    private static DocumentBlock Node(string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("delay-volterra-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

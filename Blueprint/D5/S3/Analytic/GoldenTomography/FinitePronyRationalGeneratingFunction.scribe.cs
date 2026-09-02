using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyRationalGeneratingFunctionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite exponential moment sequence has the expected finite rational "
            + "generating function on its common disk of convergence.",
        H("Finite Prony Rational Generating Function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-rational-generating-function"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/"
                        + "FinitePronyRationalGeneratingFunction."
                        + "finite_prony_rational_generating_function"),
                H("Finite Prony moments sum to their rational resolvents"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finitely many complex nodes q_j and weights m_j, define the nth "
                            + "moment c_n as the sum of m_j q_j^n. At every complex z for "
                            + "which each geometric mode q_j z has norm below one, the series "
                            + "sum of c_n z^n equals the finite sum of m_j divided by "
                            + "1 - q_j z.")),
                    Paragraph(Text(
                        "The proof applies Mathlib's geometric-series HasSum theorem to each "
                            + "mode, multiplies by its weight, and combines the finitely many "
                            + "series with hasSum_sum. The result is the analytic bridge from "
                            + "finite exponential moments to a rational transfer function.")),
                    Paragraph(Text(
                        "The theorem is pointwise on the common disk of convergence. It does "
                            + "not recover unknown nodes, quantify numerical conditioning, "
                            + "handle repeated confluent modes, or construct an infinite "
                            + "Hankel operator."))),
                DescribeRole.Theorem)),
        []));
}

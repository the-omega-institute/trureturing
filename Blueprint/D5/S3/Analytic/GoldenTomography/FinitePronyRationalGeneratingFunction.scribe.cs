using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyRationalGeneratingFunctionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/"
            + "FinitePronyRationalGeneratingFunction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite exponential moment sequence has the expected finite rational "
            + "generating function on its common disk of convergence.",
        H("Finite Prony Rational Generating Function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-generating-series-summable"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_generating_series_summable"),
                H("The finite Prony generating series is summable"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finitely many complex nodes and weights, the named series-term "
                            + "sequence is summable whenever every modal product q_j z lies "
                            + "strictly inside the unit disk.")),
                    Paragraph(Text(
                        "This theorem exposes convergence independently of the value of the "
                            + "sum. Its proof projects summability from the finite modal "
                            + "HasSum certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-prony-rational-generating-function"),
                DeclarationHandle.Create(
                    Prefix + "finite_prony_rational_generating_function"),
                H("Finite Prony moments sum to their rational resolvents"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finitely many complex nodes q_j and weights m_j, define the nth "
                            + "moment c_n as the sum of m_j q_j^n. The named predicate "
                            + "finitePronyConvergesAt records that every geometric mode q_j z "
                            + "has norm below one.")),
                    Paragraph(Text(
                        "The Lean proof is separated into four machine-checkable layers. A "
                            + "single mode is summed with Mathlib's geometric-series HasSum "
                            + "theorem, the finite family is combined with hasSum_sum, "
                            + "summability is exposed separately, and the final theorem "
                            + "identifies the sum with the rational transfer function.")),
                    Paragraph(Text(
                        "On the common convergence disk, finitePronyGeneratingSeries equals "
                            + "finitePronyRationalFunction. This is the analytic bridge from "
                            + "finite exponential moments to a rational transfer function.")),
                    Paragraph(Text(
                        "The theorem is pointwise on the common disk of convergence. It does "
                            + "not recover unknown nodes, quantify numerical conditioning, "
                            + "handle repeated confluent modes, or construct an infinite "
                            + "Hankel operator."))),
                DescribeRole.Theorem)),
        []));
}

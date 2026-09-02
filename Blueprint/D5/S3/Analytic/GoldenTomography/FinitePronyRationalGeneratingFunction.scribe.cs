using static StrataLint.Scribe.DefinitionDsl;

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
                            + "moment c_n as the sum of m_j q_j^n. The named predicate "
                            + "finitePronyConvergesAt records that every geometric mode q_j z "
                            + "has norm below one.")),
                    Paragraph(Text(
                        "The Lean proof is separated into three machine-checkable layers. A "
                            + "single mode is summed with Mathlib's geometric-series HasSum "
                            + "theorem, the finite family is combined with hasSum_sum, and the "
                            + "result is exposed through the named generating-series and "
                            + "rational-function interfaces.")),
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

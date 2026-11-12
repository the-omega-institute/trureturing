using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.DelayedCooling;

internal sealed class HistorySolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual raw integrated cooling solutions satisfy Appendix (5) and the concrete "
            + "shifted-kernel history convolution, whose integrability is derived.",
        H("From raw histories to the actual source solution"),
        Blocks(
            Paragraph(Text(
                "Write E for the concrete finite-sum quasi-exponential, and k(r)=E(r-tau). "
                    + "The source is Santos, arXiv:2611.12328v1, Appendix (5). Fix a positive "
                    + "delay at most exp(-1), an individual preparation start a at most zero, "
                    + "equilibrium q and final bath temperature c. The raw sample satisfies "
                    + "the finite-Lebesgue integrated DDE. Its raw bath is q strictly before a "
                    + "and c strictly after zero. Values at the two endpoints are unrestricted.")),
            Describe.Lean(
                DescribeId.Create("delay-history-appendix-solution"),
                DeclarationHandle.Create(Prefix + "AppendixSolution"),
                H("The finite-Lebesgue Appendix input"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sample has its pointwise constant past, satisfies Appendix (5) "
                        + "at every t at least a, and the weighted preparation integral "
                        + "at time zero is Lebesgue integrable. Separate bath integrability "
                        + "and sample regularity are not fields of this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("delay-history-raw-solution-bridge"),
                DeclarationHandle.Create(Prefix + "raw_history_solution_bridge"),
                H("Appendix (5) and the complete equilibrium tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every t at least a, T(t) equals c plus (q-c)E(t-a) plus the "
                            + "integral from a to min(0,t) of (b(s)-c)k(t-s). This is the "
                            + "literal Appendix formula with a equal to minus the individual "
                            + "preparation length. At every nonnegative t it also equals c "
                            + "plus the integral over all positive ages u of k(t+u)(b(-u)-c). "
                            + "That integrand is integrable. Neither the convolution identity "
                            + "nor its integrability is assumed as a sample field.")),
                    Paragraph(Text(
                        "The proof first derives continuity and absolute continuity from the "
                            + "integrated DDE. Integration by parts against E(t-s-tau), with "
                            + "the derivative kink split at s=t-tau, cancels the delayed "
                            + "sample integrals after a change of variables. The remaining "
                            + "equilibrium segment gives qE(t-a). Subtracting the constant "
                            + "bath contribution and truncating the postzero deviation gives "
                            + "Appendix (5). Reflection turns the finite preparation integral "
                            + "into positive ages. The exact kernel tail-mass theorem supplies "
                            + "the omitted equilibrium tail (q-c)E(t-a).")),
                    Paragraph(Text(
                        "All sample equalities are pointwise. The bath is the original raw "
                            + "representative, so an individual pointwise supremum h can be "
                            + "imposed on it without replacing it by an essential supremum. "
                            + "Each sample can use its own a and q. No common preparation "
                            + "length, step-function restriction or convolution hypothesis "
                            + "is introduced."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delay-history-appendix-equivalence"),
                DeclarationHandle.Create(Prefix + "appendix5_iff_integrated"),
                H("Appendix (5) is equivalent to the integrated DDE"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the stated delay range and equilibrium and final-bath conditions, "
                        + "a raw sample satisfies the finite-Lebesgue Appendix definition "
                        + "if and only if it satisfies the integrated DDE. To recover "
                        + "integrability of the bath on the preparation interval, multiply "
                        + "the defined weighted integrand at time zero by the continuous "
                        + "reciprocal of the positive concrete kernel, then add c. The final "
                        + "constant bath supplies the remaining finite intervals. The "
                        + "method-of-steps theorem constructs an integrated sample. Its "
                        + "Appendix representation agrees pointwise with the given sample, "
                        + "which therefore is that integrated solution. The integrated-to-Appendix "
                        + "direction uses the derived bath integrability and the actual "
                        + "kernel representation. Thus neither direction assumes sample "
                        + "regularity or an unproved solution field."))), DescribeRole.Theorem),
            Paragraph(Text(
                "The source does not fix an integral convention. Proper-Riemann and "
                    + "all-source inclusion remain unproved obligations, as do the precise "
                    + "ordinary-time/quench converse, complete event admissibility and the "
                    + "actual globally optimized balanced synchronous comparator. This is "
                    + "intermediate mathematics and makes no solved-problem or novelty claim.")))));
}

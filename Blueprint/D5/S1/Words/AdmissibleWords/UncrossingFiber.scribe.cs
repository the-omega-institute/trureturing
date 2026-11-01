using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class UncrossingFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AdmissibleWords/UncrossingFiber.";
    private static readonly LibraryNoteRef Hibi =
        LibraryNoteRef.Create("D5/L/Words/hibi1987distributivelattices");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean rows can be uncrossed by actual meet-join exchanges. Each exchange keeps "
            + "the row count and every coordinate margin, raises the rank-square energy, and a "
            + "bounded forward route reaches comparable support. Alternating complement carries "
            + "the exchange to the no-adjacent-one admissible-word carrier.",
        H("Quantitative uncrossing of admissible word fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-step-margin"),
                DeclarationHandle.Create(Prefix + "forwardStep_margin"),
                H("A meet-join step preserves every coordinate margin"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "The residual multiset is explicit, so repeated rows and empty rows are "
                        + "included. Replacing incomparable A and B by A intersect B and A union "
                        + "B preserves each coordinate's number of occupied rows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-step-energy-strict"),
                DeclarationHandle.Create(Prefix + "forwardStep_energy_strict"),
                H("An incomparable exchange raises rank-square energy"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "If a and b are the two nonempty exclusive parts of the selected rows, the "
                        + "energy increment is 2ab, hence at least two. This is the monotone "
                        + "potential used for the forward route bound."))),
                DescribeRole.Theorem,
                provenance: AssessedProvenance.FromLiterature(Hibi)),
            Describe.Lean(
                DescribeId.Create("route-to-comparable"),
                DeclarationHandle.Create(Prefix + "exists_forward_route_to_comparable"),
                H("Every finite row multiset has a bounded forward route"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "The route is built by strong induction on the remaining rank-square energy. "
                        + "It has at most floor(m times |V| squared divided by two) forward "
                        + "steps and ends at pairwise comparable support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phi-support-fence"),
                DeclarationHandle.Create(Prefix + "phi_support_fence"),
                H("Alternating complement sends admissible words to fence rows"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "The zero-based alternating complement leaves even coordinates and complements "
                        + "odd coordinates. The no-adjacent-one condition becomes the alternating "
                        + "fence inequalities, and intersections and unions remain legal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-route-bound"),
                DeclarationHandle.Create(Prefix + "adm_phi_route_bound"),
                H("The admissible carrier inherits the bounded route"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "For an actual multiset of admissible words, the transformed supports remain "
                        + "in the finite fence family throughout the constructed route. The same "
                        + "explicit bound and comparable endpoint therefore hold on the native "
                        + "carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-phi-consumer"),
                DeclarationHandle.Create(Prefix + "adm_phi_forward_consumer"),
                H("The native admissible-word consumer realizes a four-corner exchange"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "Two actual admissible words with incomparable transformed supports instantiate "
                        + "the generic residual exchange. In dimension three this includes the "
                        + "100 plus 001 exchange with its 000 and 101 meet-join endpoints."))),
                DescribeRole.Theorem))));
}

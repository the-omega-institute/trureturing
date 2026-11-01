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
                DescribeId.Create("margin-card-characterization"),
                DeclarationHandle.Create(Prefix + "margin_eq_card_iff"),
                H("A coordinate has full margin exactly when every row contains it"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "The characterization is valid for empty rows, repeated rows, and the empty "
                        + "multiset; it is the coordinate-level description of the minimum row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("comparable-margin-unique"),
                DeclarationHandle.Create(Prefix + "comparable_margin_unique"),
                H("Comparable row multisets are uniquely determined by mass and margins"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "Strong induction removes a minimum row, identified by the full-margin "
                        + "coordinates, and reconstructs the multiset from its residual."))),
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
                DescribeId.Create("forward-step-energy-gap"),
                DeclarationHandle.Create(Prefix + "forwardStep_energy_gap"),
                H("An incomparable exchange raises energy by at least two"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "Both exclusive parts are nonempty, so the exact rank-square increment is at "
                        + "least two. This is the quantitative induction step."))),
                DescribeRole.Theorem),
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
                DescribeId.Create("phi-involutive"),
                DeclarationHandle.Create(Prefix + "phi_involutive"),
                H("Alternating complement is an involution"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "Applying the parity-dependent complement twice restores every Boolean word, "
                        + "so the transformed support carrier has no information loss."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("support-phi-injective"),
                DeclarationHandle.Create(Prefix + "support_phi_injective"),
                H("Phi supports faithfully distinguish words"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "The support of the alternating complement determines the transformed word, "
                        + "and involutivity then recovers the original admissible-word input."))),
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
                DescribeId.Create("admissible-canonical-endpoint"),
                DeclarationHandle.Create(Prefix + "adm_phi_canonical_endpoint_unique"),
                H("The comparable endpoint is canonical inside the actual Phi fiber"),
                StatementSource.WithoutFormula(),
                Blocks(Paragraph(Text(
                    "Any two comparable endpoints reached by forward routes from the same "
                        + "admissible-word multiset have the same mass and coordinate margins, "
                        + "so the generic uniqueness theorem identifies them."))),
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

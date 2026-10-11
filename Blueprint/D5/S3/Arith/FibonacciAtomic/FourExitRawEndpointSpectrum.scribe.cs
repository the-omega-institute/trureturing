using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitRawEndpointSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-exit trees, a zero-to-two raw-cost obstruction, and six local tail costs.",
        H("Four-Exit Raw Endpoint Spectrum"),
        Blocks(
            Paragraph(Text(
                "A right comb has k active slots and one compensation slot. Its baseline uses B in "
                + "every active slot and R0 in the compensation slot. An exceptional member replaces "
                + "one active block by A, Y, H, or Z and uses the corresponding compensation block.")),
            Paragraph(Text(
                "The endpoint menu contains a vector with one zero and all other coordinates one "
                + "for the baseline and each Y, H, or Z member. It also contains, for each slot, three "
                + "vectors with zero at A, two at one of Y, H, or Z, and one elsewhere.")),
            Paragraph(Text(
                "For every slot and every globally correct history-dependent controller, a cost "
                + "of 8k + 16 on its A member forces a cost of at least 8k + 18 on one of its Y, H, "
                + "or Z members. Restricting the actual response tree to these four members preserves "
                + "the original controller's cost lower bound.")),
            Paragraph(Text(
                "An A-leaf query is either common to the four members or gives two sibling members "
                + "the same nonleaf reply. In the latter case, those two members must subsequently "
                + "separate. Their shared leaf labels agree, so at least one receives another nonleaf "
                + "reply before the response tree can reach singleton survivors.")),
            Paragraph(Text(
                "On the five rows (baseline, A, Y, H, Z) at any selected slot, six finite actual "
                + "response recipes attain the excess vectors (1,1,0,1,1), (1,1,1,0,1), "
                + "(1,1,1,1,0), (1,0,1,2,1), (1,0,2,1,1), and (1,0,1,1,2). "
                + "The response-cost core supplies a globally correct strategy for each recipe, "
                + "with actual costs equal to 8k + 16 plus these coordinates.")),
            Describe.Lean(DescribeId.Create("four-exit-comb-foundation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_foundation"),
                H("Structural identities for every right comb"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural slot count and arbitrary source blocks and tails, "
                    + "the third substitution acts on each block and the tail separately. The comb length "
                    + "is the sum of the block lengths and the tail length. Two combs with the same slot "
                    + "count are equal exactly when their block functions and tails are equal; they are "
                    + "nonconflicting exactly when every pair of corresponding blocks and the two tails "
                    + "are nonconflicting."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("four-exit-local-two-excess"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_two_excess"),
                H("A Zero Row Forces a Sibling of Excess Two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k, every slot j in Fin(k), and every original Strategy pi, "
                    + "cost(pi,F(k,a_j))=8k+16 implies that some sibling b in Y, H, Z has "
                    + "cost(pi,F(k,b_j)) at least 8k+18."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("four-exit-comb-slot-readout"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_slot_readout"),
                H("Readout at a comb slot"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The address consisting of j right steps, one left step, and u "
                    + "reads precisely u in slot j of an arbitrary right comb."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("four-exit-comb-tail-readout"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_tail_readout"),
                H("Readout in the compensation subtree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After k right steps the remaining address reads the "
                    + "compensation subtree of a k-slot right comb."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("four-exit-local-tail-attainment"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_tail_attainment"),
                H("Six Local Tail Costs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every selected slot, on the five rows baseline, A, Y, H, Z, "
                    + "six actual response recipes attain gains (1,1,0,1,1), (1,1,1,0,1), "
                    + "(1,1,1,1,0), (1,0,1,2,1), (1,0,2,1,1), and (1,0,1,1,2). "
                    + "Each recipe has an original globally correct Strategy with costs 8k+16 plus "
                    + "these gains on the five rows."))), DescribeRole.Theorem),
            Paragraph(Text(
                "This module supplies the local obstruction and the six local tails. "
                + "FourExitScanExtension extends the tails by scanning the other slots, "
                + "and FourExitRawParetoSpectrum gives the full-family attainment and Pareto classification.")))));

}

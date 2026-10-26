using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistory.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual coherent well-founded CH history", H("One actual coherent well-founded CH history"), Blocks(
            Paragraph(Text("The only mathematical premise is continuum=aleph-one. Stages are the countable ordinals from omega onward. Each State retains a literal Prefix through its own stage, the actual predecessor, the complete incoming initial/successor/limit evidence, incoming regular bounded F, and one whole outgoing Q with the same selected ordinary or delayed R. The entire U/B/V/nu and all original labels remain tied to their canonical births. The construction supplies no final omega-one Data, final metric, final measure, common final subsequence, or AH endpoint.")),
            Describe.Lean(DescribeId.Create("literal-cast-b-eval"),
                DeclarationHandle.Create(Owner + "cast_B_eval"), H("Whole birth B evaluation under literal equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Transporting a whole birth across equality of literal carriers preserves each original natural-indexed B clopen. This identifies the delayed source and target supports on the final realization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-advance"),
                DeclarationHandle.Create(Owner + "advance"), H("Concrete advancement of one exact past"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("advance takes CH, a stage, its exact strict past states, and pairwise coherence of that past. It returns an actual new State coherent with every earlier state. At omega it executes the actual initial predecessor. At a successor it consumes the immediate predecessor's same selected R and actual nextP. At a proper limit it forms the canonical strict Archive, proves its original Laws, and calls the actual proper-limit constructor once. It is an implemented constructor, not an extension oracle premise."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-history-existence"),
                DeclarationHandle.Create(Owner + "exists_history"), H("Existence from CH alone"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There exists one dependent family f of States, with pairwise Coherent evidence hc, such that for every stage a, f(a) is exactly advance on f restricted to strict predecessors of a and on the same hc. A guarded well-founded fixpoint first proves every entry is present and compatible; uniqueness of each present value erases the Option wrapper. No complete history, supplier of future steps, final event, or new-stage F/G hypothesis occurs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-coherence"),
                DeclarationHandle.Create(Owner + "coherent"), H("Canonical carriers, whole births and permanent arrivals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every b<a, the canonical run states are Coherent: every earlier literal carrier agrees, the later old whole birth at b equals the equality-transport of the original Q at b, each N reads the same R at its unique outgoing maximum index, and eligible I/J almost refine the corresponding earlier sets. There is no J for a row or label at or before their maximum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-execution"),
                DeclarationHandle.Create(Owner + "execution"), H("Exact strict-past unfolding"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At each stage the canonical run equals the actual advance of this same run's own strict past. This equality retains the selected data witness, beyond the proposition that some compatible state exists."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-initial"),
                DeclarationHandle.Create(Owner + "initial_execution"), H("The executed initial state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The canonical state at omega is the actual initialState constructed from H0 and its no-assumption predecessor, followed by one preparation and selection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-successor"),
                DeclarationHandle.Create(Owner + "successor_execution"), H("The same selected successor event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The canonical state at succ(b) equals nextState of the canonical state at b. Its carrier is therefore exactly the selected R at b's literal extended carrier, and its incoming evidence is that same event with literal_f, oldI and oldJ."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-limit"),
                DeclarationHandle.Create(Owner + "limit_execution"), H("The same actual proper-limit Extension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every proper successor-limit a above omega, the canonical run equals limitState of result on this same canonical strict past and its coherence proof. That result's Extension is retained whole: its I/J, DI/DJ and every-choice regular bounded F are read from the actual event. The archive contains only arrivals strictly before a and no dummy limit birth."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-proper-f"),
                DeclarationHandle.Create(Owner + "proper_f"), H("Actual regular bounded proper F"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At every countable carrier stage a, every strictly older row, eligible label and original norm-one lift sequence has a regular signed limit of total variation at most one along the actual incoming J, evaluated at each continuous real test. The same incoming event supplies regular bounded F; the weaker nextP.F is not used to recover discarded information. A metric is chosen only on the proper countable carrier to package its finite Jordan parts as regular. Regularity of the sum gives total variation regularity, finite total variation converts the real bound through ENNReal.toReal_le_toReal, and weak-dual convergence is evaluated test by test. No final metric or common final limit is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-ordinary-cofinal"),
                DeclarationHandle.Create(Owner + "ordinary_cofinal"), H("Actual ordinary treatments cofinally often"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original born row theta, whole measure label d and base, the constructed run has a later actual ordinary reservation beyond all three bounds. It exposes the selected Treatment and same R, exact row and label equations, and equality of every original Nat-indexed measure with the canonical whole birth nu(theta,d). No unused ordinary Result is archived when a delayed event is selected."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-delayed-cofinal"),
                DeclarationHandle.Create(Owner + "delayed_cofinal"), H("Intrinsic validity yields actual delayed execution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For an Intrinsic tuple on the canonical whole birth and any base, a later actual delayed reservation exposes the selected DelayedTask, same R, same DelayedCertificate and exact Matches. The natural code addresses the original B through the fixed pair/unpair codec. Source and target are distinct whole labels. Stable intrinsic semantics follow from canonical birth coherence after constructing the run; they were not recursion premises and refer to no final map or final Data."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-launch-cofinal"),
                DeclarationHandle.Create(Owner + "launch_cofinal"), H("Actual support launches from original U"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For each original support row theta, support index i and base, a later outgoing stage a creates its new V as the exact pullback of the original U(theta,i). The support row is a, while the arrival archive becomes available at succ(a). A support index is not identified with a whole signed measure label."))), DescribeRole.Theorem),
            Paragraph(Text("The final omega-one cube/AH endpoint, a concrete RawHistory supplier and its final consumer remain separate obligations; this history unit does not claim full CH or official problem completion.")))));
}

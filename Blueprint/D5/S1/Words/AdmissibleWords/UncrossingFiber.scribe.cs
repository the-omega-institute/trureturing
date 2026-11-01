using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class UncrossingFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AdmissibleWords/UncrossingFiber.";
    private static readonly LibraryNoteRef Hibi =
        LibraryNoteRef.Create("D5/L/Geometry/hibi1987distributivelattices");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite Boolean row multisets admit bounded meet-join sorting to a unique explicit "
            + "threshold multiset. Reversing and concatenating normalization routes connects each "
            + "margin fiber. Alternating complement and its inverse transport complete paths to the "
            + "native admissible-word occupancy fibers. The qualitative straightening and its "
            + "potential are classical. Straightening is attributed to Hibi (1987); the fence "
            + "poset context is attributed to Stanley, Two Poset Polytopes (1986).",
        H("Quantitative uncrossing and native admissible occupancy fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-step-margin"),
                DeclarationHandle.Create(Prefix + "forwardStep_margin"),
                H("Each residual exchange preserves coordinate counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input consists of two positive occurrences A and B and an explicit residual multiset. Replacing them by their intersection and union preserves every coordinate count, including multiplicities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("margin-card-characterization"),
                DeclarationHandle.Create(Prefix + "margin_eq_card_iff"),
                H("Full margin identifies coordinates present in every row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This characterization includes zero mass, repeated rows and empty rows and identifies the minimum row of a comparable multiset."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("comparable-margin-unique"),
                DeclarationHandle.Create(Prefix + "comparable_margin_unique"),
                H("Mass and margins uniquely determine comparable multisets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strong induction removes a minimum row, identified by the full-margin coordinates, and reconstructs the residual multiset. No inhabitedness assumption is imposed on the vertex type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-step-energy"),
                DeclarationHandle.Create(Prefix + "forwardStep_energy"),
                H("The exact rank-square energy increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Hibi),
                Blocks(Paragraph(Text("Writing the two exclusive parts as A minus B and B minus A, the energy increment is twice the product of their cardinalities. This is a classical distributive-lattice straightening potential, with no novelty claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-step-energy-gap"),
                DeclarationHandle.Create(Prefix + "forwardStep_energy_gap"),
                H("Every incomparable exchange gains at least two units of energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both exclusive parts are nonempty. The exact identity therefore supplies the quantitative decrease of the remaining energy budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("route-to-comparable"),
                DeclarationHandle.Create(Prefix + "exists_forward_route_to_comparable"),
                H("Construct an actual forward route with the initial energy charged"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strong induction on energy slack constructs k residual exchanges to comparable support and proves 2k plus the input energy is at most m times the square of the number of vertices. The floor bound k at most floor(m times the square of the number of vertices divided by two) follows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("threshold-normal-form"),
                DeclarationHandle.Create(Prefix + "sort_to_threshold"),
                H("The sorting endpoint is the explicit threshold multiset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Hibi),
                Blocks(Paragraph(Text("For an actual input M of mass m and counts c(v), row j indexed by Fin m contains v exactly when m minus c(v) is at most j.val. The multiset retains all m rows, including repeated and empty rows. Its mass and counts agree with M, its support is comparable, and uniqueness identifies it with the constructed sorting endpoint. The bound retains the initial energy; no novelty claim is made for this classical normal form or quantitative estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("threshold-family"),
                DeclarationHandle.Create(Prefix + "thresholdRows_family"),
                H("An actual sorting route proves threshold-row feasibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Binary closure under intersection and union suffices. The route places each threshold row in the original family; arbitrary independently specified margins are not assumed feasible. Empty families, empty vertex types and zero mass remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-margin-common-comparable"),
                DeclarationHandle.Create(Prefix + "same_margin_common_comparable"),
                H("Equal-margin configurations normalize to one comparable endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two bounded forward routes are constructed separately and their endpoints are identified by comparable-margin uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-margin-connected"),
                DeclarationHandle.Create(Prefix + "same_margin_connected"),
                H("Reverse and concatenate the actual residual-exchange paths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Hibi),
                Blocks(Paragraph(Text("ExchangePath uses Mathlib ReflTransGen on residual exchanges with legal family endpoints. The proof converts each constructed normalization route to such a path, reverses the second, and concatenates. The monotone budget applies to forward sorting routes only; it is not asserted for arbitrary undirected paths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exchange-path-invariants"),
                DeclarationHandle.Create(Prefix + "exchangePath_invariants"),
                H("All reachable intermediate row states stay in the same fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every path prefix preserves family membership, mass and each coordinate count. Forward and reverse steps both retain the same explicit residual exchange semantics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phi-support-fence"),
                DeclarationHandle.Create(Prefix + "phi_support_fence_iff"),
                H("Native admissibility is equivalent to the fence inequalities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zero-based alternating complement leaves even coordinates unchanged and complements odd coordinates. AdmissibleCount.adm_iff_no_adjacent_true supplies the shared adjacency characterization of the native recursive Adm n predicate. This is equivalent to the alternating fence upper-set inequalities on transformed supports, for every n including zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-fence-bijection"),
                DeclarationHandle.Create(Prefix + "admFenceEquiv"),
                H("Every fence row has a legal inverse native word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse unphi takes a row characteristic function and applies alternating complement. Both inverse equations hold on the full Boolean carriers. Restricting gives a bijection between actual Adm n words and fence rows, so arbitrary intermediate fence rows also decode legally. Original admissible supports are not asserted union-closed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phi-original-counts"),
                DeclarationHandle.Create(Prefix + "phiRows_margin"),
                H("Transformed counts follow from original occupancies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The occupancyCount is the multiset sum of original Boolean occupied coordinates. Phi counts equal c(i) on even coordinates and m minus c(i) on odd coordinates, with repetitions counted. Thus equality of original mass and occupancies implies equality of transformed margins."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-phi-consumer"),
                DeclarationHandle.Create(Prefix + "adm_phi_forward_consumer"),
                H("Pull every residual lattice move back to native word configurations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fence-family forward step decodes to NativeForwardStep: two actual word occurrences a and b are replaced by unphi of the intersection and union of their transformed supports, with exactly the same residual word multiset. The resulting words satisfy native Adm n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-path-invariants"),
                DeclarationHandle.Create(Prefix + "nativePath_invariants"),
                H("Native paths preserve legality and original occupancy counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("NativePath is Mathlib ReflTransGen of the symmetric closure of actual native residual exchanges. Every reachable state is admissible and has the original mass and each original occupancy count; this holds for every prefix and both step directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-route-bound"),
                DeclarationHandle.Create(Prefix + "adm_phi_route_bound"),
                H("Construct the complete canonical native sorting endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward route reaches the threshold multiset after Phi and satisfies the initial-energy and floor bounds. Its complete pullback is a NativePath to nativeCanonical M. Every threshold row decodes to Adm n, re-encoding the endpoint recovers exactly the threshold multiset, and any comparable forward endpoint equals it. Canonical comparability is asserted after Phi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-fiber-common-endpoint"),
                DeclarationHandle.Create(Prefix + "adm_phi_fiber_common_endpoint"),
                H("Equal original occupancy fibers are connected on the all-n native carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary multisets of native Adm n words with equal original mass and occupancyCount at every coordinate, the theorem constructs a genuine undirected NativePath, proves equality of their canonical endpoints after Phi, exposes a bounded forward normalization and its native pullback, and proves legality and original-fiber invariants at every reachable intermediate state. The n equals three exchange 100 plus 001 with 000 plus 101 is a concrete instance of the native move; it does not restrict the theorem scope."))),
                DescribeRole.Theorem))));
}

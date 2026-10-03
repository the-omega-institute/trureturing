using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class FiniteGraphProbabilityLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite graph vertex laws are classified by positive-fiber anchor laws, with a unique flip-invariant lift.",
        H("Finite Graph Probability Lifts"),
        Blocks(
            Describe.Lean(DescribeId.Create("phi"),
                DeclarationHandle.Create(Prefix + "phi"),
                H("Differential and component anchors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite simple graph, choose one root in every connected component. "
                    + "The map Phi sends a vertex bit configuration to its realizable edge label "
                    + "and its component-root anchor vector. PMF is the finite discrete probability "
                    + "representation used below; its support is exactly the positive point masses."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phi-bijective"),
                DeclarationHandle.Create(Prefix + "phi_bijective"),
                H("Every realizable label has one lift per anchor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Phi is a bijection for every finite simple graph, including the empty graph, "
                    + "disconnected graphs, and isolated vertices. The finite cycle-space fiber "
                    + "bijection supplies the unique lift for each realizable label and anchor."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("component-flip"),
                DeclarationHandle.Create(Prefix + "componentFlip"),
                H("Component flip action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A component bit vector acts by adding its bit on every vertex in that "
                    + "component. It fixes the edge differential, translates the anchor vector, "
                    + "and therefore acts on each Phi fiber by anchor translation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("component-flip-laws"),
                DeclarationHandle.Create(Prefix + "componentFlip_edgeLabel"),
                H("Flips preserve edge labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The edge label of a flipped configuration is unchanged because adjacent "
                    + "vertices lie in the same connected component and the added bit occurs twice."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("component-flip-anchor-law"),
                DeclarationHandle.Create(Prefix + "componentFlip_rootAnchors"),
                H("Flips translate roots"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each chosen component root, the anchor changes by the corresponding "
                    + "component bit."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("probability-classification"),
                DeclarationHandle.Create(Prefix + "phi_probability_lift_classification"),
                H("Positive-fiber conditional classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a PMF nu on the realizable labels. Vertex PMFs with differential marginal "
                    + "nu are in bijection with conditional PMFs q_y on anchors indexed only by "
                    + "y in nu.support. The inverse lift samples y from nu, samples its q_y anchor, "
                    + "and applies the inverse of Phi; both inverse laws are part of this equivalence. "
                    + "Zero-mass labels receive no arbitrary kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("probability-point-masses"),
                DeclarationHandle.Create(Prefix + "probability_lift_point_masses"),
                H("Point masses and zero-mass fibers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For y in nu.support and anchor a, the point mass of the unique lifted "
                    + "configuration Phi inverse (y,a) is nu(y) times q_y(a). For y outside "
                    + "the support every configuration in that fiber has point mass zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-lift"),
                DeclarationHandle.Create(Prefix + "uniformLift"),
                H("The uniform conditional lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical lift uses PMF.uniformOfFintype on the finite anchor space "
                    + "at every positive label. This is a faithful finite discrete probability "
                    + "measure: every anchor has mass the reciprocal of the anchor-space cardinality."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-flip-invariant"),
                DeclarationHandle.Create(Prefix + "uniform_lift_flip_invariant"),
                H("Uniform lift is invariant under every component flip"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The uniform anchor PMF is translation invariant, so the canonical lift is "
                    + "fixed by all component flips."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unique-flip-invariant"),
                DeclarationHandle.Create(Prefix + "flip_invariant_lift_unique"),
                H("Exactly one flip-invariant lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Among all vertex PMFs with marginal nu, exactly one is invariant under all "
                    + "component flips. Its conditional anchor law on every positive-mass label "
                    + "is uniform. The exact point masses and independent fair component bits "
                    + "are established by flip_invariant_positive_fiber_fair_bits below."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-fiber-uniform"),
                DeclarationHandle.Create(Prefix + "flip_invariant_positive_fiber_uniform"),
                H("Uniformity on every positive fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any flip-invariant lift and any positive label y, the extracted conditional "
                    + "anchor PMF equals PMF.uniformOfFintype on the full anchor space."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-fiber-fair-bits"),
                DeclarationHandle.Create(Prefix + "flip_invariant_positive_fiber_fair_bits"),
                H("Conditional independence and fairness of component bits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any flip-invariant lift and any positive label y, fix a finite set S of "
                    + "connected components and prescribe one bit on each component in S. The "
                    + "conditional cylinder probability is exactly (1/2) raised to |S|: Lean "
                    + "expresses this as the point mass of the conditional anchor PMF mapped by "
                    + "restriction to S. The proof identifies its extensions with the freely chosen "
                    + "bits on the complement of S and counts them. Taking S to be a singleton "
                    + "gives probability 1/2 for either bit, and the cylinder formula is the product "
                    + "of these probabilities, establishing mutual conditional independence. The "
                    + "same theorem gives each complete anchor vector mass (1/2) raised to c(G). "
                    + "The empty cylinder has probability one; for the empty graph c(G) is zero "
                    + "and the unique empty anchor vector has mass one."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class UnsignedStarInvariantSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Incidence/UnsignedStarInvariantSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed integral lifts need not preserve unrestricted sparsity: invariant integer support is attained by a pointwise invariant maximum cut.",
        H("Invariant Integer Support and Original Indexed Cuts"),
        Blocks(
            Paragraph(Text("Let Gamma be an arbitrary, possibly infinite group. The existing loopless Edges V X retains every original edge ID, including parallel IDs. "
                + "The reviewed IndexedAction supplies vertexPerm, edgePerm and unordered endpoint preservation; orientations may swap. "
                + "Write F=g.starMap, pi=F.range.mkQ, t=pi(1_X), R(b)=representative g b=1_X+F(b), "
                + "K(c)=cutEdges g c and U(c)=K(c)'s complement. The integer colorPotential c is -1 on true and 0 on false. "
                + "The quotient uses the actual integer range. Except for the explicitly general transport/core helpers, the fixed-fiber results assume "
                + "(g.graphAfterDeleting empty).Connected and its nonbipartiteness. Only the extremum theorem requires finite original V and X.")),
            Describe.Lean(DescribeId.Create("pointwise-invariance"), DeclarationHandle.Create(Prefix + "Invariant"),
                H("Pointwise Fixed Functions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Definition: Invariant sigma f means f(sigma gamma i)=f(i) for every gamma and i, for arbitrary index and value types. "
                    + "For Bool this fixes each color; preservation up to a color swap does not satisfy it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinate-transport"), DeclarationHandle.Create(Prefix + "invariant_iff_mem_invariants"),
                H("Inverse-Coordinate Representation Transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed helper transport: for any sigma and integer function a, Invariant sigma a is equivalent to membership in "
                    + "(coordinateRep sigma).invariants. Substitute gamma's inverse in the pointwise equality. No graph or finiteness hypothesis enters."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-potential"), DeclarationHandle.Create(Prefix + "invariant_representative_iff"),
                H("Every Actual Potential of a Fixed Representative Is Fixed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixed-potential inference: under connected nonbipartite original hypotheses, R(b) is edge-fixed if and only if b is vertex-fixed. "
                    + "Cancel the fixed all-ones term, transport by F equivariance, and apply the supplied integer injectivity of F. "
                    + "The converse uses equivariance alone. This proves invariance of the actual b, without a correction or averaging."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-class-fiber"), DeclarationHandle.Create(Prefix + "class_eq_iff_representative"),
                H("The Actual Integral t-Fiber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Quotient helper transport: for every integer z, pi(z)=t if and only if there exists integer b with R(b)=z. "
                    + "This is membership of z-1_X in F.range, with no connectedness, injectivity or finiteness assumption; neither saturation nor rational potentials enter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unique-fixed-fiber"), DeclarationHandle.Create(Prefix + "fixed_fiber_iff"),
                H("Unique Invariant Integral Potentials"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derived fixed-fiber consequence: under connected nonbipartite hypotheses, z is edge-fixed and pi(z)=t exactly when "
                    + "there exists a unique integer b satisfying both vertex invariance and R(b)=z. Quotient membership gives existence, the preceding inference gives invariance, "
                    + "and F injectivity gives uniqueness. No type is assumed finite here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("invariant-compression"), DeclarationHandle.Create(Prefix + "fixed_support_compression"),
                H("Compression Inside Each Fixed Integer Support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every fixed integer z with pi(z)=t, the same connected nonbipartite hypotheses give a pointwise invariant c with "
                    + "vertex-fixed p=colorPotential c, edge-fixed R(p), pi(R(p))=t, p(v) in {0,-1}, R(p)(i) in {-1,0,1}, "
                    + "and support(R(p))=U(c) contained in support(z). The load-bearing inference retains the supplier's sign witness "
                    + "c(v)=decide(0<2*b(v)+1): equal b-values give equal colors, so invariant b gives invariant c. "
                    + "The all-integer odd-sign subset argument and exact color support/bounds are consumed supplier mathematics, not reproved results."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-support-criterion"), DeclarationHandle.Create(Prefix + "fixed_support_criterion"),
                H("Exact Criterion for Any Original-ID Support Set"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary D subset X, existence of fixed integer z with pi(z)=t and support(z) contained in D is equivalent to "
                    + "existence of pointwise invariant c with U(c) contained in D. This consequence compresses z forward and uses R(colorPotential c) backward. "
                    + "D need not be invariant; V and X need not be finite. Ordinary bipartiteness of the remainder is insufficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attained-invariant-optimum"), DeclarationHandle.Create(Prefix + "attained_invariant_support_maxcut"),
                H("Attained Support Minimum and Invariant Maximum Cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With finite original V and X, the theorem constructs invariant c whose p=colorPotential c is fixed and 0/-1-valued, "
                    + "and whose R(p) is fixed, represents t and is {-1,0,1}-valued. Its support cardinality is IsLeast among ALL fixed integer "
                    + "t-representatives and also IsLeast among D.ncard for D admitting invariant d with U(d) contained in D. "
                    + "K(c).ncard is IsGreatest among invariant cut sizes, and support(R(p)).ncard=Fintype.card X-K(c).ncard. "
                    + "Finite max_image on invariant Bool functions constructs c; constant false makes the set nonempty. Compression gives the lower bound "
                    + "for every integer input, and the supplier's color support identity gives attainment. All original multiplicities count; no optimum is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("invariant-core"), DeclarationHandle.Create(Prefix + "invariantCore"),
                H("Whole Orbits Contained in D"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Definition: invariantCore sigma D={i : every sigma gamma i lies in D}. "
                    + "It retains only complete orbits contained in D, rather than every orbit meeting D. The definition needs no graph or finiteness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("core-subset"), DeclarationHandle.Create(Prefix + "invariantCore_subset"),
                H("The Core Lies in D"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed set helper: invariantCore sigma D is contained in D, by the identity group element."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("core-universal-property"), DeclarationHandle.Create(Prefix + "subset_invariantCore_iff"),
                H("Largest Invariant Subset"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed set transport: if membership in S is invariant under sigma, then S is contained in invariantCore sigma D "
                    + "if and only if S is contained in D. Every translate of an element of S remains in S."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-support-core"), DeclarationHandle.Create(Prefix + "fixed_support_core_criterion"),
                H("Arbitrary Deletions Reduce to Their Invariant Core"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the connected nonbipartite hypotheses, a fixed integer t-representative supported in arbitrary D exists exactly when "
                    + "some invariant c has U(c) contained in invariantCore edgePerm D. This is the support criterion transported through the core universal property: "
                    + "a fixed vector's support is invariant. A partially deleted orbit cannot be treated as fully deleted."))), DescribeRole.Theorem),
            Paragraph(Text("Private consumed helpers: invariant_representative transports supplier equivariance; invariant_colorPotential transports colors to integer values; "
                + "invariant_sign_cut applies the strengthened supplier odd_sign_cut's equal-value property. The patch exposes color_support and color_bounds unchanged, "
                + "strengthens odd_sign_cut while preserving its old consumers, and exposes IndexedAction.starMap_equivariant. "
                + "The reviewed compiled action/injectivity interface at Git 10e23a4a1e40a497ed2dc4183b694cac85050af2 is used; full fixed-cokernel lifting/descent is not used here.")),
            Paragraph(Text("For finite original V and X under the retained connected nonbipartite hypotheses, the supplied native fixed-cokernel argument explains why fixed classes admit integral fixed lifts; it does not promise a sparsest unrestricted lift is fixed. "
                + "The attained formula measures that support cost. As native consequences, a vertex-transitive action makes every invariant coloring constant and forces "
                + "full original support; within these original hypotheses, the trivial action recovers the existing ordinary support/MaxCut formula. "
                + "These are illustrations, not added Lean example declarations. Prior edge-transitive classifications, odd-cycle gaps and orbit-cokernel results are reused.")),
            Paragraph(Text("Attribution: the supplied native proof, Sections 1-5, SHA256 a92cff8d9829617a663f07a5a8576fed5e88049de0805eb61431db62084f3c31, "
                + "and the preserved Lean source package e375be2a9a9a48876a5b8c2a1a9641902d9d9042342c18ccabd227d4ae554899. Existing UnsignedStarSupport and UnsignedStarTorsion supply the integer carrier and ordinary support arithmetic. "
                + "Formal truth is carried by the compiled declarations and their standard axiom closures; descriptions distinguish new content from consumed transports. No external novelty is asserted.")))));
}

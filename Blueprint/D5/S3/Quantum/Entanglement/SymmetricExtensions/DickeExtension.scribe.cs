using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class DickeExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Star and complete graph Bose symmetric fully PPT extensions of unnormalized Dicke diagonal operators.",
        H("Dicke diagonal extension cones"),
        Blocks(
            Paragraph(Text("The register set I and local alphabet L are finite; r is the cardinality of I. A computational basis index "
                + "is a function from I to L, so matrices act on the actual tensor product of the local "
                + "complex spaces. Two selected registers a and b are distinct and ordered. "
                + "Every partial trace below is unnormalized.")),
            Node("edgeSplit", "Splitting the actual tensor factors",
                Seq(Call("edgeSplit", X("a"), X("b")), Colon, Sp, Open, X("I"), To, X("L"), Close,
                    Sp, Equiv, Sp, Open, X("L"), Times, X("L"), Close, Times,
                    Open, Call("Rest", X("a"), X("b")), To, X("L"), Close),
                "Rest(a,b) is the subtype of registers different from both a and b. "
                + "The equivalence sends x to ((x(a),x(b)), x restricted to Rest(a,b)). "
                + "Its inverse fills a and b with the ordered pair and all other sites with the complement function. "
                + "This is a bijection of the standard tensor basis, with no change of local basis.",
                DescribeRole.Definition, false),
            Node("edgeMarginal", "The unnormalized two-register marginal",
                Seq(Sub(Call("M", X("a"), X("b"), X("E")), X("u"), X("v")), Eq,
                    new Formula.Subscript(Sum, X("c")),
                    Sub(X("E"), Call("fill", X("u"), X("c")), Call("fill", X("v"), X("c")))),
                "M(a,b,E) is partialTraceRight of E reindexed by the inverse factor split. "
                + "The sum is over every computational basis label of the complement, including its single empty "
                + "label when there are exactly two registers. There is no dimension factor.",
                DescribeRole.Definition, false),
            Node("dickeVector", "The two-particle Dicke vectors",
                Seq(Sub(X("D"), X("i"), X("i")), Eq, Tensor(Sub(X("e"), X("i")), Sub(X("e"), X("i"))),
                Sp, Comma, Sp,
                    Sub(X("D"), X("i"), X("j")), Eq,
                    new Formula.Fraction(
                        Seq(Tensor(Sub(X("e"), X("i")), Sub(X("e"), X("j"))), Plus,
                            Tensor(Sub(X("e"), X("j")), Sub(X("e"), X("i")))),
                        Seq(Sqrt, Grp(D(2)))), Sp, Open, X("i"), Neq, X("j"), Close),
                "Local labels are Fin(n), corresponding to the usual labels one through n. "
                + "The diagonal vector has one unit entry. For distinct labels the only two entries "
                + "are the positive real coefficient one over the square root of two.",
                DescribeRole.Definition, true),
            Node("dickeOperator", "The full unnormalized Dicke cone",
                Seq(Rho, Eq, new Formula.Subscript(Sum, Seq(X("i"), Leq, X("j"))),
                    Sub(X("Y"), X("i"), X("j")), Sp,
                    Sub(X("D"), X("i"), X("j")),
                    new Formula.Power(Sub(X("D"), X("i"), X("j")), Star)),
                "The coefficients are arbitrary real numbers at the definition level. "
                + "The equivalence theorem restricts every upper-triangular coefficient to be nonnegative. "
                + "Each summand is its coefficient times the outer product of the actual Dicke vector "
                + "and its complex conjugate. No coefficient sum or trace is fixed; all coefficients may vanish.",
                DescribeRole.Definition, true),
            Node("FullyPPT", "Every proper nonempty PPT cut",
                Seq(Call("FullyPPT", X("E")), Iff, Forall, Sp, X("S"), Subseteq, X("I"), Comma, Sp,
                    Seq(Emptyset, Neq, X("S"), Neq, X("I")), Implies,
                    Call("PSD", new Formula.Power(X("E"), Sub(X("T"), X("S"))))),
                "S ranges over all subsets of the register set. The condition applies to each nonempty "
                + "proper S. At the matrix-entry level partialTransposeOn exchanges the row and column "
                + "labels exactly at the sites of S, in the standard tensor basis.",
                DescribeRole.Definition, true),
            Node("leafProjector", "The symmetric leaf projector",
                Seq(Call("leafProjector", X("root")), Eq, Sub(X("P"), X("L")), Eq,
                    Tensor(X("I"), Sub(Pi, Seq(X("r"), Minus, D(1))))),
                "The distinguished root is fixed. The projector is the uniform permutation average "
                + "over the setwise stabilizer of its singleton. Such permutations fix the root and permute "
                + "all remaining registers. This is the identity on the root factor times the orthogonal "
                + "projector onto the symmetric tensor power of the leaves.",
                DescribeRole.Definition, true),
            Node("StarExtension", "The star extension predicate",
                WitnessFormula(false),
                "E is positive semidefinite on all r registers, is fixed by the genuine leaf-projector "
                + "sandwich, and has marginal rho on each ordered edge from the root to a distinct leaf. "
                + "Every proper nonempty partial transpose of this same E is positive semidefinite.",
                DescribeRole.Definition, true),
            Node("CompleteExtension", "The complete graph extension predicate",
                WitnessFormula(true),
                "E is positive semidefinite on the same r registers and is fixed by the full Bose-projector "
                + "sandwich. Its marginal is rho on every ordered pair of distinct registers. "
                + "All proper nonempty PPT cuts use this same E in the original standard basis.",
                DescribeRole.Definition, true),
            Node("pairSymmetricProjector", "The actual symmetric pair projector",
                Seq(Call("pairSymmetricProjector"), Eq,
                    new Formula.Fraction(Seq(D(1), Plus, Call("flip")), D(2))),
                "The flip exchanges the two local tensor factors in the ordered product basis. "
                + "This is the orthogonal projector onto their symmetric subspace. Bose support means "
                + "the two-sided sandwich by this projector equals rho; mere conjugation invariance is weaker.",
                DescribeRole.Definition, true),
            Node("StarExtensionCore", "Star extensions without a PPT requirement",
                CoreFormula(false),
                "This predicate requires positivity, the actual root-times-symmetric-leaves support sandwich, "
                + "and rho on every ordered root-to-leaf marginal. It places no condition on partial transposes "
                + "and fixes no trace. The original StarExtension predicate still includes FullyPPT.",
                DescribeRole.Definition, false),
            Node("CompleteExtensionCore", "Complete extensions without a PPT requirement",
                CoreFormula(true),
                "This predicate requires positivity, the actual full Bose support sandwich, and rho on every "
                + "ordered pair of distinct registers. It places no condition on partial transposes and fixes no trace. "
                + "The original CompleteExtension predicate still includes FullyPPT.",
                DescribeRole.Definition, false),
            Node("support_of_connected_graph", "Connected graphs of supported marginals",
                Seq(Call("Connected", X("G")), Land, Call("PSD", X("E")), Land,
                    Call("BoseEdges", X("G"), X("E")), Implies,
                    Call("Bose", X("E")), Land, Call("AllOrderedMarginalsEqual", X("E"))),
                "For every finite register type and finite local alphabet, each edge of a connected "
                + "simple graph has its actual two-register marginal supported by the symmetric pair projector. "
                + "Positivity then forces full Bose support. All ordered marginals are equal, including "
                + "reversed pairs; the marginal values need not be supplied in advance. The proof inducts "
                + "over actual graph walks to propagate transposition invariance of every column. "
                + "This is the Hansenne-Xu-Kraft-Guehne support mechanism, with no new priority claim. "
                + "Disconnected components, higher-body hypotheses and conjugation-only leaves require "
                + "their separate bridges; this theorem does not assert them.",
                DescribeRole.Theorem, true),
            Node("componentGroup", "Permutations within connected components",
                Seq(Call("componentGroup", X("G")), Eq,
                    Call("ComponentPreservingPermutations", X("G"))),
                "A permutation belongs to this subgroup exactly when every vertex is reachable from "
                + "its image in G. Vertices cannot move between components; an isolated vertex is fixed. "
                + "The definition applies also to the empty graph and the empty register type.",
                DescribeRole.Definition, false),
            Node("componentProjector", "The component permutation projector",
                Seq(Sub(Pi, X("G")), Eq, Call("Average", Call("componentGroup", X("G")), X("Q"))),
                "This is the uniform average of the actual tensor-register permutation matrices over "
                + "componentGroup G. The tensor factorization into symmetric projectors on every "
                + "connected component is proved in BoseComponentProjector.factorization. "
                + "All singleton components remain present.",
                DescribeRole.Definition, false),
            Node("component_support_of_edges", "Support on every graph component",
                Seq(Call("PSD", X("E")), Land, Call("BoseEdges", X("G"), X("E")), Implies,
                    Sub(Pi, X("G")), X("E"), Sub(Pi, X("G")), Eq, X("E")),
                "For any finite simple graph, positive E with Bose-supported edge marginals is "
                + "supported by the component permutation projector. The proof propagates column "
                + "invariance along graph walks, generates all component-preserving permutations by "
                + "reachable transpositions, and uses the existing finite-group averaging theorem. "
                + "No factor or correlation between distinct components is discarded. The support "
                + "propagation mechanism is attributed to Hansenne-Xu-Kraft-Guehne.",
                DescribeRole.Theorem, false),
            Node("edges_iff_component_support", "Exact component support characterization",
                Seq(Call("PSD", X("E")), Implies, Open,
                    Call("BoseEdges", X("G"), X("E")), Iff,
                    Sub(Pi, X("G")), X("E"), Sub(Pi, X("G")), Eq, X("E"), Close),
                "The characterization holds for every finite graph and every positive semidefinite E. "
                + "The reverse direction uses the fact that each graph-edge transposition fixes the "
                + "component projector, then computes the actual ordered marginal and its symmetric "
                + "pair-projector sandwich. Connectedness and normalization are not assumed.",
                DescribeRole.Theorem, false),
            Node("support_of_bose_root_marginals", "Support from arbitrary Bose root marginals",
                Seq(Call("PSD", X("E")), Land, Call("BosePair", Rho), Land,
                    Open, Forall, X("i"), Neq, X("root"), Comma,
                    Call("M", X("root"), X("i"), X("E")), Eq, Rho, Close,
                    Implies, Call("Bose", X("E")), Land,
                    Open, Forall, X("a"), Neq, X("b"), Comma,
                    Call("M", X("a"), X("b"), X("E")), Eq, Rho, Close),
                "The register type is any finite type with a chosen root and the local alphabet is any finite type. "
                + "For a positive semidefinite E, Bose-supported root marginals force full Bose support "
                + "and equality of all ordered marginals. No leaf support, PPT, strict positivity, inverse, "
                + "or trace normalization is assumed. The proof lifts zero antisymmetric marginal weight "
                + "through the existing tensor trace duality and zero-weight support-face theorem, then uses "
                + "star transpositions and the existing ordered-marginal covariance proof. The marginal-to-global "
                + "support mechanism is prior work of Hansenne-Xu-Kraft-Guehne, main page 4 and Appendix D "
                + "Lemma 8 of arXiv:2108.02732v1. This formal generalization is not a priority claim.",
                DescribeRole.Theorem, true),
            Node("support_of_leaf_invariance", "Conjugation invariance of leaves suffices",
                Seq(Call("PSD", X("E")), Land, Call("LeafConjugationInvariant", X("E")), Land,
                    Call("BosePair", Call("M", X("root"), X("leaf"), X("E"))), Implies,
                    Call("Bose", X("E")), Land, Call("AllOrderedMarginalsEqual", X("E"))),
                "Choose distinct root and leaf registers. Assume only that conjugating E by every "
                + "register permutation fixing the root leaves E invariant, together with positivity "
                + "and Bose support of that one root-leaf marginal. Relabeling the complement trace "
                + "gives the same supported marginal at every root edge. The root support theorem then "
                + "gives full Bose support and every ordered marginal equal to the original one. "
                + "Leaf-subspace support is not a premise.",
                DescribeRole.Theorem, false),
            Node("same_matrix_core", "The identical matrices without PPT",
                Seq(Call("BosePair", Rho), Implies,
                    Open, Call("StarExtensionCore", X("root"), Rho, X("E")), Iff,
                    Call("CompleteExtensionCore", Rho, X("E")), Close),
                "For every individual E, on any finite register set with a chosen root and finite local alphabet, "
                + "the two no-PPT predicates are equivalent whenever rho is supported by the actual pair "
                + "symmetric projector. The forward direction obtains full support and all ordered marginals "
                + "from the root marginals; the reverse uses inclusion of the full symmetric subspace in "
                + "the root-times-symmetric-leaves subspace. The theorem does not assert existence of an "
                + "extension for every rho. It includes zero and singular rho, local dimension one, exactly "
                + "two registers and arbitrary unnormalized traces.",
                DescribeRole.Theorem, false),
            Node("same_matrix", "The identical matrices with fully PPT cuts",
                Seq(Call("BosePair", Rho), Implies,
                    Open, Call("StarExtension", X("root"), Rho, X("E")), Iff,
                    Call("CompleteExtension", Rho, X("E")), Close),
                "Under the same finite-type and actual Bose support hypotheses as same_matrix_core, "
                + "the original fully PPT predicates select the same individual E. Every nonempty proper "
                + "cut is retained on that E. This is a pointwise equality, so it preserves the witness, "
                + "its trace and all singular boundary cases. It does not assert universal extendibility.",
                DescribeRole.Theorem, false),
            Node("result", "Equality of the extension cones",
                Seq(Forall, Sp, X("n"), Geq, D(1), Comma, Sp, Forall, Sp, X("r"), Geq, D(2), Comma, Sp,
                    Forall, Sp, X("Y"), Comma, Sp,
                    Open, Forall, Sp, X("i"), Comma, X("j"), Comma, Sp,
                    X("i"), Leq, X("j"), Implies, Sub(X("Y"), X("i"), X("j")), Geq, D(0), Close, Implies, Sp, Open,
                    Open, Exists, Sp, X("E"), Comma, Sp, Call("StarExtension", D(0), Rho, X("E")), Close,
                    Iff,
                    Open, Exists, Sp, X("E"), Comma, Sp, Call("CompleteExtension", Rho, X("E")), Close, Close),
                "Here n and r are natural numbers, Y is an arbitrary real n by n array, and i and j range "
                + "over Fin(n). The operator rho is the Dicke sum above. This is an equivalence of existence predicates "
                + "for every register count at least two and every local dimension at least one. "
                + "In the forward direction the complete graph witness is literally the star witness. "
                + "The antisymmetric two-particle projector annihilates each Dicke vector. "
                + "Trace duality lifts its zero marginal weight to zero weight of the actual tensor-placed "
                + "projector on E. The zero_weight_support_face theorem gives both one-sided annihilations "
                + "without requiring an inverse or trace normalization. Thus every root transposition fixes "
                + "every column of E. Star transpositions generate all permutations, so the columns lie in "
                + "the full symmetric subspace. The orthogonal projector and Hermiticity give the full "
                + "sandwich, and relabeling actual complement indices makes all ordered edge marginals equal. "
                + "Every PPT inequality is retained verbatim. Conversely the full symmetric subspace is "
                + "contained in the root-times-symmetric-leaves subspace, and complete edges include all "
                + "star edges. The argument includes zero coefficients, singular witnesses, n=1 and r=2. "
                + "The resolution target is exactly Gulati-Nechita-Park, arXiv:2509.15201v4, Question 8.20; "
                + "current journal question wording and worldwide absence of a prior solution are unverified.",
                DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gnp-2025-v4-question-8-20-dicke-extensions"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("dicke-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Seq(params Formula[] items)
    {
        var spaced = new System.Collections.Generic.List<Formula>();
        foreach (var item in items)
        {
            if (spaced.Count != 0) spaced.Add(Sp);
            spaced.Add(item);
        }
        return F.Seq(spaced.ToArray());
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula Sub(Formula value, params Formula[] indices) =>
        new Formula.Subscript(value, Seq(indices));
    private static Formula Tensor(Formula a, Formula b) => Call("tensor", a, b);
    private static Formula CoreFormula(bool complete)
    {
        var p = complete ? Sub(Pi, X("r")) : Sub(X("P"), X("L"));
        var marginals = complete
            ? Seq(Forall, X("a"), Neq, X("b"), Comma,
                Call("M", X("a"), X("b"), X("E")), Eq, Rho)
            : Seq(Forall, X("i"), Neq, X("root"), Comma,
                Call("M", X("root"), X("i"), X("E")), Eq, Rho);
        return Seq(complete ? Call("CompleteExtensionCore", Rho, X("E"))
                : Call("StarExtensionCore", X("root"), Rho, X("E")),
            Iff, Call("PSD", X("E")), Land, p, X("E"), p, Eq, X("E"), Land,
            Open, marginals, Close);
    }
    private static Formula WitnessFormula(bool complete)
    {
        var p = complete ? Sub(Pi, X("r")) : Sub(X("P"), X("L"));
        var marginals = complete
            ? Seq(Forall, Sp, X("a"), Comma, X("b"), Comma, Sp,
                X("a"), Neq, X("b"), Implies, Call("M", X("a"), X("b"), X("E")), Eq, Rho)
            : Seq(Forall, Sp, X("i"), Comma, Sp, X("i"), Neq, X("root"), Implies, Sp,
                Call("M", X("root"), X("i"), X("E")), Eq, Rho);
        var predicate = complete
            ? Call("CompleteExtension", Rho, X("E"))
            : Call("StarExtension", X("root"), Rho, X("E"));
        return Seq(predicate, Iff,
            Call("PSD", X("E")), Land, p, X("E"), p, Eq, X("E"), Land,
            Open, marginals, Close, Land, Call("FullyPPT", X("E")));
    }
}

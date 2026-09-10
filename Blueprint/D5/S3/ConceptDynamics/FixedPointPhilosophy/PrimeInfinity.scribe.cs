using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.FixedPointPhilosophy;

internal sealed class PrimeInfinityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.";
    private static Formula S => F.Id("s");
    private static Formula B => F.Id("B");
    private static Formula L => F.Id("L");
    private static Formula U => F.Id("U");
    private static Formula Q => F.Id("Q");
    private static Formula T => F.Id("t");
    private static Formula Stage => Call("L", T);
    private static Formula StageCore => Call("core", Stage);
    private static Formula Limit => Call("limitCore", L);
    private static Formula Nodes => Call("unionNodes", L);
    private static Formula PrimeUnion => Call("PrimeUnion", B, L);
    private static Formula Thm => Call("Thm", S);
    private static Formula Primes(Formula core) => Call("Prime", B, core);
    private static Formula Frozen(Formula core) => Call("N", core);
    private static Formula Intersection(Formula a, Formula b) => Call("inter", a, b);
    private static Formula ClosureType => Call("ClosureOperator", Call("Set", Call("P", S)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exhaustive witness chains have a unique core limit and infinitely many primes.",
        H("Prime Infinity and the Witnessed Core Limit"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("global-admissible-chains"),
                DeclarationHandle.Create(Prefix + "GeneratedChain"),
                H("Total admissible transformations"), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a proof system s and a sequence L of legal finite snapshots. "
                    + "A transformation is a total function on all legal ledgers. It is admissible "
                    + "when every input is extended, with every old witness retained. GeneratedChain(L) "
                    + "requires each successor L(t+1) to equal T(L(t)) for some such globally "
                    + "admissible T. The frozen sets grow monotonically, and witnesses on overlapping "
                    + "stages agree by comparison at max(i,j). Stuttering is allowed, and a dependent "
                    + "and its prerequisites may enter in the same stage.")))),
            Theorem("extension-realization", "extends_iff_admissible",
                "Extensions are exactly attainable admissible steps", ExtensionFormula(),
                "For an extension from one snapshot to another, define a total transformation "
                + "sending that particular input to the extension and fixing every other input. "
                + "It is globally admissible. The reverse implication evaluates admissibility "
                + "at the given input. Together with core extension, this identifies the "
                + "attainability preorder and its antisymmetric frozen-core projection."),
            Describe.Remark(
                DescribeId.Create("coherent-union-witness"),
                DeclarationHandle.Create(Prefix + "limit_witness_agrees"),
                H("The raw union witness"), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write unionNodes(L) for the union over all natural-number stages of N(L(t)). "
                    + "Glue the coherent witnesses on these sets by Set.iUnionLift. For a proposition "
                    + "in N(L(t)), the resulting witness equals its stored witness at t. Define the "
                    + "raw union edge from the references of this glued witness. Its incoming edges "
                    + "at an old target agree exactly with the old incoming edges. Reference closure "
                    + "keeps all those predecessors in the old stage.")))),
            Theorem("raw-path-reflection", "limit_path_iff", "Old targets have no new ancestors",
                ChainFormula(Seq(Forall, Sp, T, Colon, Sp, F.Id("Nat"), Comma, Sp,
                    F.Id("a"), Comma, Sp, F.Id("b"), Colon, Sp, Call("P", S), Comma, Sp,
                    F.Id("b"), Sp, InMacro, Sp, Frozen(Stage), Sp, Rightarrow, RowBreak, Grp(),
                    Call("StrictReachable", Call("limitEdge", L), F.Id("a"), F.Id("b")),
                    Sp, Iff, Sp, Call("StrictReachable", Call("E", StageCore),
                        F.Id("a"), F.Id("b")))),
                "Every old frozen stage is predecessor-closed for the raw union relation, giving "
                + "a dependency filtration. The least predecessor-closed set containing a target "
                + "contains each vertex on a path into it. Induction backward from an old target "
                + "then reflects every path into its old snapshot, using the incoming-edge equality. "
                + "The forward implication does not assume that the union is already acyclic."),
            Describe.Remark(
                DescribeId.Create("lawful-core-construction"),
                DeclarationHandle.Create(Prefix + "limitCore"),
                H("The lawful core"), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Acceptance, permitted axioms, and reference closure of the union witness follow "
                    + "from any stage containing its target. A cycle in the raw union would reflect "
                    + "into such a stage and contradict its acyclicity. This constructs a witnessed "
                    + "core with frozen set unionNodes(L); its edges are exactly the union of the "
                    + "stage edges. For every p already present at t, Anc(limitCore(L),p) equals "
                    + "Anc(core(L(t)),p), so each present node has finitely many ancestors.")))),
            Theorem("core-least-upper-bound", "limit_isLeastUpperBound",
                "The core is the least upper bound",
                ChainFormula(Seq(Forall, Sp, Q, Colon, Sp, Call("WitnessedCore", S), Comma,
                    RowBreak, Grp(), Call("CoreExtends", Limit, Q), Sp, Iff, Sp,
                    Forall, Sp, T, Colon, Sp, F.Id("Nat"), Comma, Sp,
                    Call("CoreExtends", StageCore, Q))),
                "Every stage extends into the union core. If another core Q extends all stages, "
                + "it contains every union node and agrees with its witness at a containing stage. "
                + "Thus the union core extends into Q. CoreLimit(L,U) denotes precisely these "
                + "upper-bound and leastness clauses. Antisymmetry of core extension gives uniqueness "
                + "on (N,E,w). No order or limit is imposed on registered frontiers."),
            Theorem("exhaustion-equivalence", "exhausts_iff_iUnion_eq",
                "Exhaustion is equality with the theorem set",
                FamilyFormula(Seq(Call("Exhausts", L), Sp, Iff, Sp, Nodes, Sp, Eq, Sp, Thm)),
                "Exhausts(L) means that each p in Thm(s) occurs in N(L(t)) at some natural-number "
                + "stage t. Every frozen node already belongs to Thm(s), by its accepted permitted "
                + "witness, which proves the reverse inclusion. For a generated exhaustive chain, "
                + "the same finite growing sets form a Set.FiniteExhaustion of Thm(s). Existence "
                + "of an exhaustive chain for an arbitrary proof system is not asserted."),
            Theorem("finite-total-prime-bound", "finite_total_primes_bound",
                "The finite-total-prime contradiction", FiniteBoundFormula(),
                "Write PrimeUnion(B,L) for the union over all stages of Prime(B,core(L(t))), and "
                + "call this set R. Suppose R is finite. Each of its members has an accepted permitted "
                + "witness, so R is contained in Thm(s). Finite prime generation and monotonicity of B "
                + "put every N(L(t)) in B(R). Their union therefore lies in B(R) intersect Thm(s). "
                + "Strict binding makes that intersection a proper subset of Thm(s), contradicting "
                + "exhaustion. These inclusions hold for any family of legal finite snapshots."),
            Theorem("limit-prime-union", "limit_prime_eq_iUnion",
                "The limit primes are exactly the union of the stage primes",
                ClosureChainFormula(Seq(Primes(Limit), Sp, Eq, Sp, PrimeUnion)),
                "For a proposition in an old stage, the ancestor set is exactly unchanged in the "
                + "limit, hence so is membership in B of that ancestor set. Every limit node occurs "
                + "at some stage. These two facts give both inclusions without any continuity or "
                + "finitarity assumption on B."),
            Theorem("complete-prime-infinity", "prime_infinity_complete",
                "Prime infinity with the unique exhaustive core", CompleteFormula(),
                "For every proof system, every closure operator B, and every globally admissible "
                + "exhaustive chain satisfying strict binding, the union of the stage primes is "
                + "infinite. There is exactly one witnessed core U satisfying CoreLimit(L,U), "
                + "N(U)=Thm(s), and Prime(B,U)=PrimeUnion(B,L). The finite-total-prime contradiction "
                + "proves infinitude; witness gluing and the least-upper-bound property give the "
                + "core, while ancestor stability gives its prime set."),
            Theorem("limit-prime-infinity", "limit_prime_infinite",
                "Infinitely many primes in the limit",
                ClosureFamilyFormula(Seq(Hypotheses(), Sp, Rightarrow, RowBreak, Grp(),
                    Call("Infinite", Primes(Limit)))),
                "The prime-set equality transfers infinitude to the limit. Since primes belong "
                + "to the frozen set, this exhaustive limit cannot be a finite snapshot. Any "
                + "disjoint frontier can be attached to its core, including the empty set, without "
                + "changing ancestry or primes; this does not select a limit of the frontiers."),
            Describe.Remark(
                DescribeId.Create("structural-reading"),
                DeclarationHandle.Create(Prefix + "prime_infinity_complete"),
                H("The structural reading"), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Euclid and Godel analogy concerns the obstruction that a finite collection "
                    + "of generators cannot cover every theorem by binding closure. It supplies "
                    + "neither a formal equivalence between those classical arguments nor a theorem "
                    + "about a particular collection of actual proof-assistant declarations. "
                    + "The result is conditional on the displayed structural hypotheses. It adds "
                    + "no global countability, kernel soundness, semantic consistency, universal "
                    + "certificate availability, or convergence assumption.")))))));

    private static DocumentBlock Theorem(string id, string name, string title,
        Formula formula, string proof) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula FamilyFormula(Formula body) => Disp(Seq(
        Forall, Sp, S, Colon, Sp, F.Id("ProofSystem"), Comma, Sp,
        L, Colon, Sp, F.Id("Nat"), Sp, To, Sp, Call("LegalLedger", S), Comma,
        RowBreak, Grp(), body));

    private static Formula ClosureFamilyFormula(Formula body) => FamilyFormula(Seq(
        Forall, Sp, B, Colon, Sp, ClosureType, Comma, RowBreak, Grp(), body));

    private static Formula ChainFormula(Formula body) => FamilyFormula(Seq(
        Call("GeneratedChain", L), Sp, Rightarrow, RowBreak, Grp(), body));

    private static Formula ClosureChainFormula(Formula body) => ClosureFamilyFormula(Seq(
        Call("GeneratedChain", L), Sp, Rightarrow, RowBreak, Grp(), body));

    private static Formula Strictness()
    {
        Formula finiteSet = F.Id("R");
        return Seq(Open, Forall, Sp, finiteSet, Colon, Sp, Call("Set", Call("P", S)), Comma,
            Sp, Call("Finite", finiteSet), Sp, Land, Sp, finiteSet, Sp, Subseteq, Sp, Thm,
            Sp, Rightarrow, Sp, Intersection(Call("B", finiteSet), Thm),
            Sp, Subset, Sp, Thm, Close);
    }

    private static Formula Hypotheses() => Seq(Call("GeneratedChain", L), Sp, Land, Sp,
        Strictness(), Sp, Land, Sp, Call("Exhausts", L));

    private static Formula CompleteFormula() => ClosureFamilyFormula(Seq(
        Hypotheses(), Sp, Rightarrow, RowBreak, Grp(), Call("Infinite", PrimeUnion),
        Sp, Land, Sp, Exists, Bang, Sp, U, Colon, Sp, Call("WitnessedCore", S), Comma,
        RowBreak, Grp(), Call("CoreLimit", L, U), Sp, Land, Sp, Frozen(U), Sp, Eq, Sp, Thm,
        Sp, Land, Sp, Primes(U), Sp, Eq, Sp, PrimeUnion));

    private static Formula FiniteBoundFormula() => ClosureFamilyFormula(Seq(
        Strictness(), Sp, Land, Sp, Call("Finite", PrimeUnion), Sp, Rightarrow,
        RowBreak, Grp(), PrimeUnion, Sp, Subseteq, Sp, Thm, Sp, Land, Sp,
        Open, Forall, Sp, T, Colon, Sp, F.Id("Nat"), Comma, Sp,
        Frozen(Stage), Sp, Subseteq, Sp, Call("B", PrimeUnion), Close, Sp, Land, Sp,
        RowBreak, Grp(), Nodes, Sp, Subseteq, Sp, Intersection(Call("B", PrimeUnion), Thm),
        Sp, Land, Sp, Intersection(Call("B", PrimeUnion), Thm), Sp, Subset, Sp, Thm));

    private static Formula ExtensionFormula()
    {
        Formula first = F.Id("M");
        Formula second = F.Id("N");
        Formula transform = F.Id("T");
        return Disp(Seq(Forall, Sp, S, Colon, Sp, F.Id("ProofSystem"), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, Call("LegalLedger", S), Comma,
            RowBreak, Grp(), Call("Extends", first, second), Sp, Iff, Sp,
            Exists, Sp, transform, Colon, Sp, Call("LegalLedger", S), Sp, To, Sp,
            Call("LegalLedger", S), Comma, Sp, Call("Admissible", transform), Sp, Land, Sp,
            second, Sp, Eq, Sp, Call("T", first)));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Safety;

internal sealed class InvariantSafetyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inductive invariant makes every finitely reachable state safe.",
        H("Invariant Safety"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inductive-invariants-certify-finite-executions"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Safety/InvariantSafety.invariant_safety"),
                H("Inductive invariants certify finite executions"),
                StatementSource.FromAuthor(InvariantSafetyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let R be a transition relation, I0 the initial set, J an invariant, "
                            + "and S the safe set. The hypotheses expose all three invariant "
                            + "conditions: I0 is contained in J, J is contained in S, and every "
                            + "R-successor of a state in J remains in J.")),
                    Paragraph(Text(
                        "A reflexive-transitive R path represents an arbitrary finite execution. "
                            + "Direct induction with Relation.ReflTransGen.head_induction_on "
                            + "propagates membership in J from the actual initial state to the "
                            + "endpoint, where containment in S gives safety.")),
                    Paragraph(Text(
                        "The relation need not be deterministic, terminating or confluent. "
                            + "The conclusion concerns each finite path; it asserts no fairness "
                            + "or eventual completion."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("A stronger conditional material-preservation model"), Blocks(
                Paragraph(Text(
                    "Material-preserving operations illustrate how to obtain the one-step premise "
                        + "from effects rather than assuming safety of each successor. The following "
                        + "seven-effect model requires exhaustive preservation, absence of active "
                        + "users at a discarded location and continuous exclusion. These are "
                        + "stronger conditional premises, not eligibility requirements for "
                        + "disposable-worktree cleanup. Authorized deletion may discard local-only "
                        + "work and need not be a transition of this relation. Let M, P "
                        + "and J be arbitrary types of immutable material versions, recovery "
                        + "locations and actual jobs. A state has required material R, confirmed "
                        + "remote material D, local support L in M times P, active use U in J "
                        + "times P, and qualified exclusion holders H in J times P. These are mathematical "
                        + "observations of one realization, not an additional stored record. "
                        + "An item is recoverable when it is in D or has some support in L. "
                        + "Safety requires this for every item of R.")),
                Paragraph(Text(
                    "A location p is held when some pair (j,p) belongs to H. Qualification "
                        + "at p means that every material item supported there is in D and no "
                        + "job has active use there. This checks all discarded support, including "
                        + "support for items outside R. The stronger invariant combines safety "
                        + "with qualification of every held location. Locations may denote a "
                        + "directory, a private recovery reference or another affected resource; "
                        + "they are not necessarily whole trees. The material relation represents "
                        + "protected obligations and recovery effects; it does not make every "
                        + "intermediate keystroke a permanently required historical version. "
                        + "Mapping an actual edit requires identifying the still-required items "
                        + "and their genuine reconstruction supports.")),
                Paragraph(Text(
                    "The elementary relation has seven effects. Entry adds (j,p) to U only "
                        + "when p is not held. Production at an active, unheld location adds a "
                        + "new required version m together with support (m,p). Confirmation adds "
                        + "m to D. Acquisition adds (j,p) to H at an unheld, qualified location. "
                        + "Inheritance adds (k,p) to H from an existing holder (j,p). Exit "
                        + "removes only pairs labelled by the exiting job from U and H. A "
                        + "destructive effect at a held p removes the pairs (m,p) for m in an "
                        + "arbitrary selected cut, without changing R or D. No effect takes "
                        + "safety or the stronger invariant as its enabling condition. "
                        + "Acquisition denotes the final qualification boundary of an operation "
                        + "already protected by real exclusion, rather than a lock-system call. "
                        + "Preliminary lock acquisition or failed inspection authorizes no "
                        + "destructive effect and must leave material intact; it contributes "
                        + "no qualified holder to H.")),
                Paragraph(Text(
                    "Each effect preserves the stronger invariant by set membership laws. "
                        + "Production supplies the new item's local witness. Confirmation only "
                        + "enlarges remote retention. Entry and production cannot affect a held "
                        + "location. Acquisition supplies qualification at its new location; "
                        + "inheritance obtains it from the parent holder. Exit removes activity "
                        + "and holders while retaining all material. Destruction leaves an old "
                        + "support witness unless it cuts that pair; in that case qualification "
                        + "supplies remote retention of the item. It also only shrinks the "
                        + "support set, so every surviving held location stays qualified. "
                        + "Applying invariant_safety to this relation, with the stronger "
                        + "invariant as both J and S, proves preservation through every finite "
                        + "interleaving of these seven effects, including a prefix interrupted between "
                        + "destructive effects.")),
                Paragraph(Text(
                    "Exclusion is continuous in this stronger argument. While any holder at p survives, "
                        + "new entry and new material production at p are disabled, and confirmed "
                        + "retention is unchanged or enlarged. After the last holder exits, "
                        + "further destruction requires a fresh acquisition and qualification. "
                        + "Partial destruction therefore needs no rollback assumption. A "
                        + "one-time sample without exclusion has a countermodel: start with an "
                        + "empty qualified location, admit a writer, produce one unconfirmed "
                        + "item there, then delete its sole support using the obsolete sample. "
                        + "The final state loses a required item.")),
                Paragraph(Text(
                    "The allowed relation also has nonempty successful cases. A location "
                        + "supporting a remotely retained item can be qualified and removed "
                        + "while a different location has an active writer and an unconfirmed "
                        + "item. A child inheriting the first location's exclusion can survive "
                        + "the parent's exit and perform the destructive effect. Its later exit "
                        + "releases the last holder. Thus preservation permits concurrent work, "
                        + "recovery and actual disposal; it does not require permanent refusal.")))),
            new DocumentBlock.Section(H("Attributed checkpoints with independent editing"), Blocks(
                Paragraph(Text(
                    "For a checkpoint, fix an authorized set A of file coordinates, a "
                        + "protected set K containing A, and a stable snapshot v. Represent "
                        + "working bytes by w and the authorized overlay of a private operation "
                        + "index by a function k taking either no selected entry or a value. "
                        + "The private index is initialized from the fixed HEAD commit; k starts "
                        + "empty relative to that base, while the full private index contains "
                        + "the base entries. Initially w agrees with v on K. Unrelated entries "
                        + "in the real shared index do not enter k and do not prevent the "
                        + "checkpoint from starting. They remain in the real index.")),
                Paragraph(Text(
                    "During the operation an independent edit replaces w at a coordinate "
                        + "outside K. A staging step replaces k at a coordinate of A with its "
                        + "current working value. Other insertion into the private index and changes to protected "
                        + "working coordinates are excluded throughout the operation. Function "
                        + "update laws prove that working stability and exact index attribution "
                        + "are preserved by these two effects; invariant_safety extends this "
                        + "to an arbitrary finite staging/editing path. If every coordinate of "
                        + "A is staged at the end, k records exactly those coordinates with "
                        + "their snapshot values. Comparing the resulting tree with HEAD may "
                        + "omit authorized no-ops. Under exact private-index consumption, "
                        + "the committed diff therefore contains only stable authorized changes.")),
                Paragraph(Text(
                    "The boundary includes a countermodel: insert an unrelated entry into k "
                        + "between staging and commit. Individual index updates can each be "
                        + "mutually exclusive, yet the final index violates attribution. "
                        + "The operation must protect its private index, stable working footprint "
                        + "and branch base through staging and commit consumption. Independent "
                        + "working edits and unrelated real-index staging may continue. Deletion entries "
                        + "can be represented by a value in the value type; absence from the "
                        + "change unit is a separate index option. Unmerged stages and a changing "
                        + "base require additional representation and coordination; they cannot "
                        + "silently be collapsed into this function.")),
                Paragraph(Text(
                    "Git ref advancement and real-index synchronization are separate effects. "
                        + "After advancing the ref, the adapter replaces only attributed real-index "
                        + "entries from its private index, using native index locking and preserving "
                        + "unrelated staging. A failure between those effects can leave HEAD advanced "
                        + "with stale attributed entries. A retry builds a fresh private index from "
                        + "current HEAD and synchronizes the authorized scope even when its tree "
                        + "equals HEAD. Success, including unchanged status and finalization with "
                        + "authorized paths, requires that synchronization to succeed. An equal "
                        + "tree alone does not certify completion. Abandoned indexes are not "
                        + "restored over current shared staging. This correspondence is an "
                        + "implementation obligation checked with native Git fixtures, not a "
                        + "consequence of the function model.")),
                Paragraph(Text(
                    "Semantic authorization can read other coordinates. K must contain "
                        + "the target and both states' actual read "
                        + "sets. "),
                    Ref("D5/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation.two_state_locality_yields_incremental_preservation"),
                    Text(" supplies equivalence of such a local property under independent "
                        + "editing: equality to the same snapshot gives endpoint byte equality "
                        + "on K, hence an unchanged target and no changed dependency there. "
                        + "The protected set can be strictly larger than the staged set while "
                        + "a third coordinate changes. Disjoint file names alone do not establish independence "
                        + "of read-sensitive operations. "),
                    Ref("D5/S0/Rewriting/HindleyRosen.reflTransGen_commute_of_strong_commute"),
                    Text(" lifts the commuting squares of unconditional disjoint-coordinate "
                        + "writes to arbitrary finite write blocks. Neither result supplies "
                        + "a merge procedure for overlapping edits.")))),
            new DocumentBlock.Section(H("Exit, durability and the realization boundary"), Blocks(
                Paragraph(Text(
                    "In the conditional model, for distinct jobs j and k, exit of j leaves every active-use and holder "
                        + "pair labelled k unchanged. An inherited descriptor is represented "
                        + "by a holder pair for the child, rather than by the parent's continued "
                        + "existence. Exit also leaves R, D and L unchanged. Even an exit leaving "
                        + "no activity and no exclusion holder can leave a required item only "
                        + "locally supported. Automatic release establishes no publication.")),
                Paragraph(Text(
                    "For finite material sets, "),
                    Ref("D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss.artifact_sufficient_iff_every_kill_zero_byte_loss"),
                    Text(" gives the separate complete-local-loss boundary: with artifact set "
                        + "D and session set equal to all local material, zero required loss "
                        + "after erasing the latter is equivalent to R being contained in D. "
                        + "Its insufficiency direction exhibits nonempty loss. In this "
                        + "application local Git commits belong to local support until "
                        + "confirmation, even though they are persistent on local disk. A "
                        + "single participant's exit does not perform this erasure. For the "
                        + "actual recovery guarantee, R can be the authorized commit units whose "
                        + "remote retention has been confirmed. Then R is contained in D, so loss "
                        + "of all local support leaves those units recoverable. If R also includes "
                        + "local-only items, the zero-loss conclusion need not hold; authorized "
                        + "worktree deletion may discard them.")),
                Paragraph(Text(
                    "Remote support means a genuine reconstruction route, including required "
                        + "metadata and object dependencies. Publication resolves the named "
                        + "remote's push destination; push and fresh confirmation refer to the "
                        + "same endpoint. Multiple push destinations are refused before writing. "
                        + "Confirmation observes a remote branch tip and establishes that the "
                        + "required exact commit is that tip or an ancestor of it. A successful "
                        + "process exit, push invocation or stale tracking ref is insufficient. "
                        + "Retention must remain valid through each recovery relying on it. "
                        + "Rebuilding additionally depends on the complete reconstruction "
                        + "relation and the required toolchain; confirmation alone promises "
                        + "neither future remote availability nor reconstruction progress.")),
                Paragraph(Text(
                    "Cooperative editing protects overlapping writes and actual semantic "
                        + "reads; compound Git operations coordinate their affected index and "
                        + "ref scopes. Disjoint editing remains concurrent. OS descriptor "
                        + "lifetime releases operation exclusion without an LLM unlock; children "
                        + "that continue a protected operation must retain its descriptors or "
                        + "enter the protocol themselves. Normal finalization follows host "
                        + "joining of this task's writers, checkpoints stable authorized paths "
                        + "and confirms publication. Other participants can continue. Abnormal "
                        + "exit and lock release establish no publication fact. These scoped "
                        + "coordination premises do not create a session-long writer lease or "
                        + "a deletion-exclusion requirement.")),
                Paragraph(Text(
                    "Actual worktree disposal uses user-directed selection and the Git lock/time "
                        + "rule: a selected unlocked tree may be removed; a locked tree requires "
                        + "the existing 24-hour lock duration. Automatic selection has its own "
                        + "Git-update age and behind-count conditions, which named removal bypasses. "
                        + "Target identity, main-tree protection, nested registration checks and "
                        + "accurate partial-failure reporting remain. Active programs, cwd, open "
                        + "resources, protocol participation, cache use, remote confirmation and "
                        + "exhaustive local preservation do not qualify or veto deletion. "
                        + "Ordinary non-worktree artifacts and local ref retirement retain their "
                        + "independent policies. The seven-effect argument does not certify this "
                        + "disposal rule; remote-confirmed recovery is its separate consequence. "
                        + "No mathematical statement here verifies the Git/OS realization, "
                        + "eventual publication or fairness.")))))));

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Apply2(Formula relation, Formula left, Formula right) =>
        Seq(relation, Open, left, Comma, Sp, right, Close);

    private static Formula InvariantSafetyFormula()
    {
        Formula relation = F.Id("R");
        Formula initial = F.Id("I0");
        Formula invariant = F.Id("J");
        Formula safe = F.Id("S");
        Formula x0 = F.Id("x0");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula state = F.Id("X");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula stateSet = Seq(Operatorname, Grp(F.Id("Set")), Open, state, Close);
        Formula relationType = new Formula.TypeArrow(
            state, new Formula.TypeArrow(state, prop));

        return Disp(Seq(
            Forall, Sp, state, Colon, Sp, type, Comma, Sp,
            relation, Colon, Sp, relationType, Comma, RowBreak,
            initial, Comma, Sp, invariant, Comma, Sp, safe, Colon, Sp, stateSet,
            Comma, RowBreak,
            initial, Sp, Subseteq, Sp, invariant, Sp, Land, Sp,
            invariant, Sp, Subseteq, Sp, safe, Sp, Land, RowBreak,
            Open, Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Member(x, invariant), Sp, Land, Sp, Apply2(relation, x, y), Sp,
            Rightarrow, Sp, Member(y, invariant), Close, RowBreak,
            Rightarrow, Sp, Forall, Sp, x0, Comma, Sp, x, Colon, Sp, state,
            Comma, RowBreak,
            Member(x0, initial), Sp, Land, Sp,
            Operatorname, Grp(F.Id("ReflTransGen")), Open, relation, Close,
            Open, x0, Comma, Sp, x, Close, Sp, Rightarrow, Sp,
            Member(x, safe), Dot));
    }
}

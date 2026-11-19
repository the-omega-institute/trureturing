using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class SalinasSchmeisOmegaChainExtensionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/salinasschmeis2026omega");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Question 2.32 has no universal least omega-chain-partitionable extension.",
        H("Refutation of the least omega-chain-partitionable extension question"),
        Blocks(
            Definition("IsOmegaChain", "Parts order-isomorphic to omega", IsOmegaChainFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Page 2: “An ω-chain of a poset P is a subset of P that is order-isomorphic to ω under the ordering inherited from P.” The formula uses the inherited order on the subtype C."),
            Definition("OmegaPartitionable", "Partitions into omega-chains", OmegaPartitionableFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Question 2.3, page 3: “Given a poset P with no maximal element, when can the maximal family D of disjoint ω-chains in P given by Lemma 2.1 be taken such that ⋃D = P? That is, when can P be partitioned into ω-chains?” The formula records a covering disjoint family whose members satisfy IsOmegaChain."),
            Definition("IsExtension", "Induced order extension", IsExtensionFormula(),
                AssessedProvenance.FromLiterature(Source),
                "An extension is represented by an order embedding, so the original order is preserved and reflected."),
            Definition("claim", "Question 2.32", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                "Question 2.32, page 14: “Let P be a poset. Does there exist a minimal extension Q of P which can be partitioned into ω-chains? Here by minimal we mean that if Q′ is any extension of P which can be partitioned into ω-chains, then Q is order-isomorphic to a subposet of Q′.” The encoding uses an induced order embedding for extension and a setoid partition whose parts are order-isomorphic to omega.",
                "The same source predicates accept P : Type u, a candidate Q : Type v and comparison Q′ : Type w independently. A claim instance fixes these three universe parameters; Lean does not quantify over universe levels inside Prop. The original Type0 refutation is the instance u = v = w = 0, with the original Fork and private proof suppliers. Comparison embeddings Q → Q′ have no equation requiring them to fix P. The countability and uniform finite chain-height hypotheses of the further classification concern P alone, and impose no restriction on Q′. The positive carrier P ⊕ₗ ℕ is chosen from P before the comparison universe; upward ULift order isomorphisms preserve induced embeddings and transport the literal partition to preimage parts, without shrinking P. This interface does not itself prove the positive classification or the arbitrary-candidate negative theorem.",
                "For the ordinal extension construction the independent carrier is α.ToType : Type o for α : Ordinal o, and P ×ₗ α.ToType lies in Type (max u o). Ordinal.ToType.mk applied to ⟨0, 0 < α⟩ selects the distinguished point when α ≠ 0; Ordinal.type_toType gives its order type, and upward lifting changes the represented ordinal by Ordinal.lift. The companion construction SalinasSchmeisLexicographicFiberExtension supplies the induced embedding and the literal fiber partition, including the empty base. In the ordinal case the same family is cofinal and gives a skeleton. The countable finite-height classification, explicit countable partitions, Noetherian section/shift injection, dual statements, Nat leastness boundary and finite-n skeleton obstruction remain separate proof obligations."),
            Describe.Lean(
                DescribeId.Create("incompatible"),
                DeclarationHandle.Create(Prefix + "incompatible"),
                H("An incomparable pair excludes the two targets"),
                StatementSource.FromAuthor(Disp(IncompatibleFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let Q be any partial order with no maximal element, and let x and y be "
                    + "incomparable. Choose z strictly above x. Under an order embedding into Tail, "
                    + "the images of x and y remain incomparable, so tail_forced_bound puts the "
                    + "image of y below the image of z. Reflecting gives y ≤ z. Under an embedding "
                    + "into Rays, the images of x and y now have a common upper bound; "
                    + "rays_upper_comparable and reflection contradict their incomparability. "
                    + "There is no cardinality, countability, height or common-lower-point hypothesis "
                    + "on Q. An omega partition supplies the strict successors through omega_successor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omega-partition-ulift"),
                DeclarationHandle.Create(Prefix + "omega_partition_ulift"),
                H("Lifting the inherited partition"),
                StatementSource.FromAuthor(Disp(PartitionLiftFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For an arbitrary X and any lift universe w, replace each partition part C by its preimage under "
                    + "ULift.down. The inherited order isomorphism sends c to ULift.up c. "
                    + "These parts remain nonempty, cover uniquely, and retain their omega order. "
                    + "The empty carrier uses the empty family. This transport supplies the lifted "
                    + "Rays and Tail comparison targets in the fork argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Separated rays and a merged tail are incompatible"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The separated-ray order Rays has carrier Bool × ℕ. Its relation is x ≤ y "
                    + "exactly when x = (false, 0) or both x.1 = y.1 and x.2 ≤ y.2. "
                    + "The partition consists of the two full ranges {(false, n) | n ∈ ℕ} and "
                    + "{(true, n) | n ∈ ℕ}. They are disjoint and cover Rays, and the maps "
                    + "n ↦ (false, n) and n ↦ (true, n) are order isomorphisms onto the respective "
                    + "ranges with inherited order. The fork's root and two branches map to "
                    + "(false, 0), (false, 1) and (true, 0).")),
                    Paragraph(Text(
                    "The order Tail has carrier ℕ, with x ≤ y exactly when the usual natural-number "
                    + "comparison holds and (x, y) ≠ (1, 2). Its partition consists of the ranges "
                    + "{2n | n ∈ ℕ} and {2n + 1 | n ∈ ℕ}. They are disjoint and cover Tail. "
                    + "The maps n ↦ 2n and n ↦ 2n + 1 are order isomorphisms onto these inherited "
                    + "even and odd chains: the removed comparison joins different parts. "
                    + "The fork's root and two branches map to 0, 1 and 2.")),
                    Paragraph(Text(
                    "The three-element fork thus embeds into two omega-chain-partitionable orders. "
                    + "In the separated-ray order, two points with a common upper bound are comparable. "
                    + "In the tail order obtained by removing the comparison 1 ≤ 2, a strict successor "
                    + "of one incomparable point is above the other. An omega-chain partition supplies such "
                    + "a strict successor, and order embeddings transfer the resulting comparisons back to "
                    + "the fork, producing a contradiction.")),
                    Paragraph(Text(
                    "The same obstruction applies to the literal two-element antichain. Take the "
                    + "inherited subset A = {left, right} of Fork; its order is equality. Restrict "
                    + "intoRays and intoTail along its subtype embedding. Their two images are "
                    + "(false, 1), (true, 0) in Rays and 1, 2 in Tail, respectively. For any "
                    + "admissible extension e of A, the points e(left) and e(right) are incomparable "
                    + "and omega_successor supplies a strict successor. Leastness would embed that "
                    + "extension into both targets, contradicting incompatible. Upward lifts of A "
                    + "and the targets give the same argument with independent base, candidate and "
                    + "comparison universes. These comparison maps need satisfy no equation with e. "
                    + "The original fork still has its root below both branches, making its "
                    + "undirected comparability graph connected; this is a description of its "
                    + "displayed order. The two-point consequence does not alter the original "
                    + "negative answer or its attribution.")),
                    Paragraph(Text(
                    "The universe-polymorphic application lifts the fixed Fork to Type u and lifts "
                    + "Rays and Tail to the comparison universe Type w. The candidate Q retains Type v. "
                    + "For each original partition part C, the lifted part is the preimage of C under "
                    + "ULift.down. The inherited order isomorphism sends c to ULift.up c, so the original "
                    + "omega isomorphism composes with it. Nonemptiness, unique coverage and disjointness "
                    + "are preserved. Composing the assumed comparison embeddings with ULift.down gives "
                    + "Q → Rays and Q → Tail; composing the base embedding with ULift.up gives Fork → Q. "
                    + "The general incompatible theorem applied to the branch images supplies the contradiction. This "
                    + "uses no shrinking assumption on an arbitrary carrier and assigns no new solved credit.")),
                    Paragraph(Text(
                    "The literature screen is partial. The primary source and its version history, "
                    + "successful arXiv author and text queries, MathOverflow and Zenodo searches, "
                    + "public formal-conjecture snapshots and repository results identified no matching "
                    + "settlement in the inspected scope. Citation enumeration was unavailable, several "
                    + "Zenodo endpoints were blocked, and the original MacNeille completion article was "
                    + "not independently read. Those gaps and literature completeness remain "
                    + "ASSUMED-UNVERIFIED; no worldwide novelty or exhaustive coverage is asserted."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("salinas-omega-chain-extension"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock.Describe Definition(string name, string title, Formula formula,
        AssessedProvenance provenance, params string[] prose) =>
        Describe.Lean(DescribeId.Create("definition-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks([.. prose.Select(value => Paragraph(Text(value)))]), DescribeRole.Definition);

    private static Formula IsOmegaChainFormula()
    {
        var p = F.Id("P");
        var c = F.Id("C");
        var body = Call("Nonempty", Call("OrderIso", Nat(), c));
        return All("P", TypeAt("u"), Instance("PartialOrder", p,
            All("C", Call("Set", p), Equal(Call("IsOmegaChain", c), body))));
    }

    private static Formula OmegaPartitionableFormula()
    {
        var p = F.Id("P");
        var d = F.Id("D");
        var c = F.Id("C");
        var partition = App(Qualified("Setoid", "IsPartition"), d);
        var parts = All("C", Call("Set", p),
            Implies(Member(c, d), Call("IsOmegaChain", c)));
        var body = Ex("D", Call("Set", Call("Set", p)), And(partition, parts));
        return All("P", TypeAt("u"), Instance("PartialOrder", p,
            Equal(Call("OmegaPartitionable", p), Parenthesized(body))));
    }

    private static Formula IsExtensionFormula()
    {
        var p = F.Id("P");
        var q = F.Id("Q");
        var body = Call("Nonempty", Call("OrderEmbedding", p, q));
        return All("P", TypeAt("u"), All("Q", TypeAt("v"),
            Instance("PartialOrder", p, Instance("PartialOrder", q,
                Equal(Call("IsExtension", p, q), body)))));
    }

    private static Formula ClaimBody()
    {
        var p = F.Id("P");
        var q = F.Id("Q");
        var qp = F.Id("Qprime");
        var po = F.Id("pOrder");
        var qo = F.Id("qOrder");
        var qpo = F.Id("qOrderPrime");
        var comparison = Call("Nonempty", Call("OrderEmbedding", q, qp,
            Seq(qo, Dot, F.Id("toLE")), Seq(qpo, Dot, F.Id("toLE"))));
        var least = All("Qprime", TypeAt("w"), All("qOrderPrime", Call("PartialOrder", qp),
            Implies(Call("IsExtension", p, qp, po, qpo),
                Implies(Call("OmegaPartitionable", qp, qpo), comparison))));
        var witness = Ex("Q", TypeAt("v"), Ex("qOrder", Call("PartialOrder", q),
            And(Call("IsExtension", p, q, po, qo), And(Call("OmegaPartitionable", q, qo), least))));
        return All("P", TypeAt("u"), All("pOrder", Call("PartialOrder", p), witness));
    }

    private static Formula IncompatibleFormula()
    {
        var q = F.Id("Q");
        var x = F.Id("x");
        var y = F.Id("y");
        var z = F.Id("z");
        var noMax = All("x", q, Ex("z", q, Seq(x, Sp, Lt, Sp, z)));
        var incomparable = And(new Formula.Not(Parenthesized(Seq(x, Sp, Leq, Sp, y))),
            new Formula.Not(Parenthesized(Seq(y, Sp, Leq, Sp, x))));
        var maps = All("f", Call("OrderEmbedding", q, F.Id("Rays")),
            All("g", Call("OrderEmbedding", q, F.Id("Tail")), F.Id("False")));
        return All("Q", TypeAt("u"), Instance("PartialOrder", q,
            Implies(noMax, All("x", q, All("y", q, Implies(incomparable, maps))))));
    }

    private static Formula PartitionLiftFormula()
    {
        var x = F.Id("X");
        var lift = Call("ULift", x);
        return All("X", TypeAt("u"), Instance("PartialOrder", x,
            Implies(Call("OmegaPartitionable", x), Call("OmegaPartitionable", lift))));
    }

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, F.Id(name));

    private static Formula TypeAt(string level) => Seq(F.Id("Type"), Sp, F.Id(level));

    private static Formula Nat() => F.Id("Nat");

    private static Formula Instance(string name, Formula carrier, Formula body) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket, Sp, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}

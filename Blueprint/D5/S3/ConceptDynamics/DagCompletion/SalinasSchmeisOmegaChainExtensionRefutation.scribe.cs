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
                "Question 2.3, page 2: “Given a poset P with no maximal element, when can the maximal family D of disjoint ω-chains in P given by Lemma 2.1 be taken such that ⋃D = P? That is, when can P be partitioned into ω-chains?” The formula records a covering disjoint family whose members satisfy IsOmegaChain."),
            Definition("IsExtension", "Induced order extension", IsExtensionFormula(),
                AssessedProvenance.FromLiterature(Source),
                "An extension is represented by an order embedding, so the original order is preserved and reflected."),
            Definition("claim", "Question 2.32", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                "Question 2.32, page 14: “Let P be a poset. Does there exist a minimal extension Q of P which can be partitioned into ω-chains? Here by minimal we mean that if Q′ is any extension of P which can be partitioned into ω-chains, then Q is order-isomorphic to a subposet of Q′.” The encoding uses an induced order embedding for extension and a setoid partition whose parts are order-isomorphic to omega."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Separated rays and a merged tail are incompatible"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The three-element fork embeds into two omega-chain-partitionable orders. "
                    + "In the separated-ray order, two points with a common upper bound are comparable. "
                    + "In the tail order obtained by removing the comparison 1 ≤ 2, a strict successor "
                    + "of one incomparable point is above the other. An omega-chain partition supplies such "
                    + "a strict successor, and order embeddings transfer the resulting comparisons back to "
                    + "the fork, producing a contradiction."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("definition-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula IsOmegaChainFormula()
    {
        var p = F.Id("P");
        var c = F.Id("C");
        var body = Call("Nonempty", Call("OrderIso", Nat(), c));
        return All("P", F.Id("Type"), Instance("PartialOrder", p,
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
        return All("P", F.Id("Type"), Instance("PartialOrder", p,
            Equal(Call("OmegaPartitionable", p), Parenthesized(body))));
    }

    private static Formula IsExtensionFormula()
    {
        var p = F.Id("P");
        var q = F.Id("Q");
        var body = Call("Nonempty", Call("OrderEmbedding", p, q));
        return All("P", F.Id("Type"), All("Q", F.Id("Type"),
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
        var least = All("Qprime", F.Id("Type"), All("qOrderPrime", Call("PartialOrder", qp),
            Implies(Call("IsExtension", p, qp, po, qpo),
                Implies(Call("OmegaPartitionable", qp, qpo), comparison))));
        var witness = Ex("Q", F.Id("Type"), Ex("qOrder", Call("PartialOrder", q),
            And(Call("IsExtension", p, q, po, qo), And(Call("OmegaPartitionable", q, qo), least))));
        return All("P", F.Id("Type"), All("pOrder", Call("PartialOrder", p), witness));
    }

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, F.Id(name));

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

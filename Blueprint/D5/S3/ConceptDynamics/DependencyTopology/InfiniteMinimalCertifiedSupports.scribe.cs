using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class InfiniteMinimalCertifiedSupportsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One decidable lawful propositional kernel has infinitely many globally minimal certified supports.",
        H("Infinitely many minimal supports for one proposition"),
        Blocks(
            Paragraph(Text(
                "A certified core is a finite set of formulas with an accepted proof selected at "
                + "each node, only permitted axioms, closure under the selected references, and an "
                + "acyclic selected reference graph. The support family consists of all sets arising "
                + "from such cores. Its definition permits different proofs of the same formula "
                + "in different cores.")),
            Definition("Supports", "Supports of a target",
                OverKernel(Seq(Forall, Sp, F.Id("p"), Colon, Sp, F.Id("P"), Comma, Sp,
                    Forall, Sp, F.Id("S"), Colon, Sp, Call("Set", F.Id("P")), Comma, Sp,
                    Call("Supports", F.Id("k"), F.Id("p"), F.Id("S")), Sp, Iff, Sp,
                    F.Id("p"), Sp, InMacro, Sp, F.Id("S"), Sp, Land, Sp,
                    F.Id("S"), Sp, InMacro, Sp, Call("supportFamily", F.Id("k")))),
                "The set S contains the target p and is the node set of an actual certified core. "
                + "Finiteness follows from that core; no upward closure is assumed."),
            Definition("minimalSupports", "Global inclusion minimality",
                OverKernel(Seq(Forall, Sp, F.Id("p"), Colon, Sp, F.Id("P"), Comma, Sp,
                    Call("minimalSupports", F.Id("k"), F.Id("p")), Sp, Eq, Sp,
                    OpenBrace, F.Id("S"), Colon, Sp, Call("Set", F.Id("P")), Sp, Mid, Sp,
                    Call("Minimal", Call("Supports", F.Id("k"), F.Id("p")), F.Id("S")), CloseBrace)),
                "Minimal uses inclusion on sets: S supports p, and every support T contained in S "
                + "also contains S. The comparison is with all actual supports of p. This is "
                + "minimality, with no assertion of a unique least support."),
            Definition("claim", "Unconditional finiteness",
                Seq(F.Id("claim"), Sp, Iff, Sp, OverKernel(Seq(
                    Call("SourceLaws", F.Id("k")), Sp, Implies, Sp, Forall, Sp,
                    F.Id("p"), Colon, Sp, F.Id("P"), Comma, Sp,
                    Call("Finite", Call("minimalSupports", F.Id("k"), F.Id("p")))))),
                "All four carriers range over types, and k is kernel data on those carriers. "
                + "SourceLaws requires soundness in every model of the permitted axioms, a finite "
                + "closed acyclic certificate for every proved formula, and consistency with "
                + "negation. The claim asserts finiteness for every target with no finite candidate "
                + "domain premise."),
            Definition("a", "The infinitely indexed roots",
                Seq(Forall, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
                    Call("a", F.Id("n")), Sp, Eq, Sp,
                    Call("imp", Call("atom", Call("succ", F.Id("n"))),
                        Call("atom", Call("succ", F.Id("n"))))),
                "For each natural number n, a(n) is the implication from variable n+1 to itself. "
                + "These are pairwise syntactically distinct tautologies."),
            Definition("q", "The common target",
                Seq(F.Id("q"), Sp, Eq, Sp,
                    Call("imp", Call("neg", Call("atom", D(0))), Call("neg", Call("atom", D(0))))),
                "Let r be variable zero. Using implication and falsity, disjunction u or v is "
                + "encoded as not u implies v. Thus q is not r implies not r, the encoding of "
                + "r or not r. It is a tautology and is syntactically different from every a(n). "
                + "Formula evaluation and negation are the ordinary Boolean semantics."),
            Definition("kernel", "One infinite decidable kernel",
                Seq(F.Id("kernel"), Colon, Sp, Call("KernelData", F.Id("Formula"),
                    Seq(F.Id("Nat"), Sp, Times, Sp, F.Id("Bool")), F.Id("Unit"),
                    Seq(Open, F.Id("Nat"), Sp, To, Sp, F.Id("Bool"), Close))),
                "Proof symbols are pairs (n,b) with n a natural number and b a Boolean. "
                + "The symbol (n,false) accepts exactly a(n) and has no references; (n,true) "
                + "accepts exactly q and references exactly a(n). There are no other accepted "
                + "pairs. All axiom readouts and the permitted axiom set are empty. Acceptance "
                + "uses decidable syntactic equality, and both readouts are executable. Models "
                + "are all Boolean valuations of the countable variable set."),
            Definition("pair", "The two-node family",
                Seq(Forall, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
                    Call("pair", F.Id("n")), Sp, Eq, Sp,
                    OpenBrace, Call("a", F.Id("n")), Comma, Sp, F.Id("q"), CloseBrace),
                "The set pair(n) is {a(n),q}, in the same kernel for every n."),
            Describe.Lean(
                DescribeId.Create("infinite-minimal-certified-supports-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Unconditional finiteness fails"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every n, select (n,false) at a(n) and (n,true) at q in pair(n). "
                        + "These proofs are accepted and closed. Every selected edge runs from "
                        + "a(n), of rank zero, to q, of rank one; strict increase gives acyclicity. "
                        + "Every accepted conclusion occurs in one of these finite certificates. "
                        + "Accepted formulas are true under every valuation, so the kernel is "
                        + "sound. A formula and its syntactic negation cannot both evaluate to "
                        + "true at the constant-false valuation, which proves consistency.")),
                    Paragraph(Text(
                        "Consider any actual support S of q. Its selected accepted proof at q "
                        + "must be (m,true) for some m, since no root formula equals q. Closure "
                        + "therefore forces a(m) into S. If S is contained in pair(n), syntactic "
                        + "distinctness forces m=n. Since q is also in S, S equals pair(n). "
                        + "This proves global inclusion minimality of every pair(n); in particular "
                        + "the singleton {q} is not a support. Equality of two displayed pairs "
                        + "forces equality of their root indices. The resulting injection from "
                        + "the natural numbers into minimalSupports(kernel,q) proves that this "
                        + "one family is infinite and contradicts claim.")),
                    Paragraph(Text(
                        "The generic minimal-support conclusions follow directly from order and "
                        + "finite-set results. Mathlib setOfPred_minimal_antichain applies to the "
                        + "support predicate. For a given finite support, "
                        + "exists_minimal_le_of_wellFoundedLT on finite subsets, with "
                        + "Finset.wellFoundedLT, supplies a globally minimal support below it. "
                        + "For finite D, the minimal supports contained in D lie in its powerset. "
                        + "Set.Finite.powerset gives finiteness, and Set.ncard_le_ncard together "
                        + "with Set.ncard_powerset bounds their number by two to the cardinality "
                        + "of D. These facts require neither upward closure nor a finite universe "
                        + "of propositions. The infinite construction shows precisely why the "
                        + "finite candidate-domain hypothesis cannot be omitted."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string selector, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("infinite-minimal-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula OverKernel(Formula body) => Seq(
        Forall, Sp, F.Id("P"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Forall, Sp, F.Id("Proof"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Forall, Sp, F.Id("Ax"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Forall, Sp, F.Id("Model"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Forall, Sp, F.Id("k"), Colon, Sp,
        Call("KernelData", F.Id("P"), F.Id("Proof"), F.Id("Ax"), F.Id("Model")), Comma, Sp, body);
}

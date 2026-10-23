using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class HFMemberOccurrencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/History/Spacetime/HFMemberOccurrences.";
    private static Formula Call(string name, Formula x) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body);
    private static Formula Mass(Formula x) => Call("mass", x);
    private static Formula Count(Formula x) => Call("card", Call("Occurrence", x));
    private static Formula Power(Formula n) => Seq(D(2), Caret, Grp(n));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The recursive mass of an actual hereditarily finite set counts its descending member paths.",
        H("Unfolded Occurrences in Original HF Archives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-hf-member-mass"),
                DeclarationHandle.Create(Prefix + "mass"),
                H("A total member recursion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mass is defined on the existing HFEncoding.HF by well-founded recursion on "
                    + "membership of its toZF interpretation. Each set contributes one for its root, "
                    + "then the masses of all members in the existing finite members set. Equality "
                    + "of members removes duplicates within one set. Equal descendants reached at "
                    + "different positions remain separate occurrences."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("member-mass-equation"),
                DeclarationHandle.Create(Prefix + "mass_eq"),
                H("The exact recursion equation"),
                StatementSource.FromAuthor(Disp(All("x", F.Id("HF"), Seq(
                    Mass(F.Id("x")), Eq, D(1), Plus, Sum, Underscore,
                    Grp(F.Id("y"), InMacro, Sp, Call("members", F.Id("x"))), Sp,
                    Mass(F.Id("y")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite sum is over every actual member once. Mathlib's well-founded "
                    + "membership relation supplies total recursion; HFEncoding.members_finite "
                    + "supplies the finite domain. There is no order chosen for the members and "
                    + "no common bound on the ranks or the sizes of the input sets."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-descending-occurrences"),
                DeclarationHandle.Create(Prefix + "Occurrence"),
                H("Occurrences defined independently as lists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An occurrence of x is a finite list p satisfying Descends x p. The empty "
                    + "list denotes the root. A list y :: q is admissible precisely when toZF(y) "
                    + "belongs to toZF(x) and q descends from y. This definition refers only to "
                    + "actual membership and lists; it does not refer to mass or to an auxiliary "
                    + "tree representation. In ordinal two, both [ordinal zero] and "
                    + "[ordinal one, ordinal zero] reach zero and are distinct occurrences."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-path-mass-correspondence"),
                DeclarationHandle.Create(Prefix + "occurrence_card"),
                H("Finiteness and exact occurrence count"),
                StatementSource.FromAuthor(Disp(All("x", F.Id("HF"), Seq(
                    Count(F.Id("x")), Eq, Mass(F.Id("x")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All occurrences are finite in number. Deleting the first member of a "
                    + "nonempty descending list gives a bijection between occurrences of x and "
                    + "the disjoint sum of its root and the occurrence families of its members. "
                    + "Well-founded induction proves finiteness of this disjoint sum and then "
                    + "identifies its cardinality with the recursive mass. Different first "
                    + "members occupy different summands even when later descendants coincide. "
                    + "The finite instance rules out the infinite-type zero convention for Nat.card."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-ordinal-unfolded-growth"),
                DeclarationHandle.Create(Prefix + "mass_natCode"),
                H("Every finite ordinal has exponential unfolded mass"),
                StatementSource.FromAuthor(Disp(All("n", Seq(Mathbb, Grp(F.Id("N"))), Seq(
                    Mass(Call("natCode", F.Id("n"))), Eq, Power(F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "These are the original finite von Neumann ordinal codes. Ordinal zero "
                    + "is empty and has mass one. The code of n + 1 inserts the code of n into "
                    + "the code of n. No ordinal belongs to itself, so the insertion adds exactly "
                    + "the mass of that new member to the previous mass and doubles it. Induction "
                    + "therefore gives 2 to the n for every natural n, including zero. The path "
                    + "correspondence gives the same number of actual occurrences. These codes "
                    + "are ordinals, not cumulative hierarchy levels."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-rich-code-leaf-bound"),
                DeclarationHandle.Create(Prefix + "richCode_leaf_bound"),
                H("An archived leaf bounds the complete rich code"),
                StatementSource.FromAuthor(Disp(All("x", Call("Rich", D(3)),
                    All("e", Call("Event", F.Id("x")),
                    All("n", Seq(Mathbb, Grp(F.Id("N"))), Seq(
                        Call("source", Seq(F.Id("x"), Comma, F.Id("e"))), Eq,
                        Call("of", F.Id("n")), Sp, Implies, Sp,
                        Power(F.Id("n")), Leq, Sp, Mass(Call("richCode", F.Id("x"))),
                        Sp, Land, Sp, Power(F.Id("n")), Leq, Sp,
                        Count(Call("richCode", F.Id("x"))))))))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here Event(x) is the archived event subtype of x's context, and source(x,e) "
                        + "is that event's actual source attribute. Let x be any original Rich 3, "
                        + "e any archived event and n any natural number whose source is FreeMagma.of n. "
                        + "Its source code contains the ordinal code n inside the original tagged "
                        + "Kuratowski pair. Membership bounds carry its mass through the source, "
                        + "sign, position and time tuple, the complete attribute graph, the archive "
                        + "record, the current-region pair and the selected-set pair. The actual "
                        + "path correspondence then gives the occurrence bound. Neither the current "
                        + "region nor the selection needs to contain e. The original causal graph "
                        + "and every attribute remain in the encoded object.")),
                    Paragraph(Text(
                        "A Kuratowski pair contains both operands along actual member paths, "
                        + "including the diagonal case in which its inner or outer members coincide. "
                        + "The proof therefore allows identity/attribute equality, member overlap, "
                        + "repeated sources and all collisions between nested fields. It uses no "
                        + "noncollision hypothesis and no pruning of an archive.")),
                    Paragraph(Text(
                        "For the family of Definition 497.1, take the typed event domain "
                        + "Fin N times Bool and any injective map of this domain into actual HF "
                        + "identities. TaggedPresentation transports the time i + 1, three zero "
                        + "coordinates, Boolean sign, source leaf (i + 1), and causal relation i < j "
                        + "to the exact archive. Take the entire event domain as the current region "
                        + "and any finite selected subset. For every event at layer n the theorem "
                        + "gives at least 2 to the n occurrences in the original full richCode, "
                        + "for both signs and every legal selection, including the empty set and "
                        + "the original Mobius mask. This application restricts neither identities "
                        + "nor collisions. At N = 0 the event assertions are vacuous; ordinal-zero "
                        + "and the general source-zero bound remain included.")),
                    Paragraph(Text(
                        "Mass counts unfolded set nodes. It does not count distinct hereditary "
                        + "nodes, stored shared nodes, framed bits or machine work. The asymmetric "
                        + "relation identity, uniform two-sided full-family estimates, empty "
                        + "archive value 44, literal framing and cold-run costs, identity bit "
                        + "construction and native-input separation of Theorem 497.2 require "
                        + "additional arguments. No running-time or space claim follows here."))),
                DescribeRole.Theorem))));
}

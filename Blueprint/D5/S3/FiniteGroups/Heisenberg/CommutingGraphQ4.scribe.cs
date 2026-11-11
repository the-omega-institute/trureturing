using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Heisenberg;

internal sealed class CommutingGraphQ4Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/arvind2023commuting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime p, two groups of order p to the sixth have isomorphic full commuting graphs and are not isoclinic.",
        H("Non-isoclinic pairs at every prime-sixth order"),
        Blocks(
            Describe.Lean(DescribeId.Create("commuting-qfour-exact-event"),
                DeclarationHandle.Create(Owner + "ExactEvent"), H("The exact quantified event"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("ExactEvent"), Event()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Section 9, Q4, page 40 asks: What can be said about pairs of groups with isomorphic commuting graphs? Do non-isoclinic examples exist for all orders p^6 with p prime? Only the second sentence is the assertion here. FiniteGroup is the existing bundle of a carrier type, an actual Group structure and finiteness. The graph uses every element as a vertex, with adjacency exactly unequal whole elements whose products commute. Isoclinic means compatible group isomorphisms on the central quotients and source derived subgroups, intertwining x inverse times y inverse times x times y for all representatives."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("commuting-qfour-derived-obstruction"),
                DeclarationHandle.Create(Owner + "not_isoclinic"), H("The derived groups obstruct isoclinism"),
                StatementSource.FromAuthor(Disp(All("p", Nat(), Imp(Call("NatPrime", F.Id("p")),
                    Negate(Call("Isoclinic", Carrier(Call("squareGroup", F.Id("p"))), Carrier(Call("dualGroup", F.Id("p"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take R=ZMod(p*p) and S=DualNumber(ZMod p). The groups squareGroup and dualGroup are the Heisenberg triples over R and S. Their source derived subgroups are exactly the central z-axes. In R the element with central coordinate one has nonidentity p-th power because p is nonzero modulo p*p. Every element of the S axis is killed by the p-th power. A group isomorphism preserves powers, so no derived-group isomorphism exists. This already prevents isoclinism and needs no classification of the full centre."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("commuting-qfour-result"),
                DeclarationHandle.Create(Owner + "result"), H("An affirmative answer for every prime"),
                StatementSource.FromAuthor(Disp(Event())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Use the same two coefficient rings for each prime. Each ring has p*p elements, hence each triple group has order p^6. The prime-two case is included throughout; there is no division by two. The residue-chart construction supplies a bijection of the two-coordinate bases preserving equality of cross products for every pair. A coefficient bijection supplies the third coordinate. Their product is a bijection on whole triples, so distinctness is preserved even for equal bases with different z coordinates. Equality xY=Xy is exactly group commutation, yielding an isomorphism of the full simple commuting graphs.")),
                    Paragraph(Text("The three disjoint base charts are (u,ut), (us,u) with u a unit and s in the maximal ideal, and pairs in that ideal. Within a primitive chart, equality of fine slopes decides incidence. The two primitive charts are never incident to each other. Between a finite-slope chart and an ideal vector (j(a),j(b)), incidence is b=res(t)*a. Between the other primitive chart and an ideal vector it is a=0. Every two ideal vectors are incident. The zero vector therefore remains incident to every vector. This common relation retains the fine slope and its residue rather than identifying them.")),
                    Paragraph(Text("The generic group, power, cardinality and derived-axis APIs are an attributed compatible Tau Ceti port. They do not supply the graph-incidence bijection. The source already reports examples at primes two, three and five. The theorem covers every natural prime and does not claim a classification, minimal order, worldwide priority or a complete answer to the first sentence of Q4. The bounded source and supplier search does not establish exhaustive later-literature coverage."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("arvind-2023-commuting-graph-q4"), ResolutionKind.Proved)))));

    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Negate(Formula a) => Seq(Neg, Sp, Par(a));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Carrier(Formula g) => Call("Carrier", g);
    private static Formula Event()
    {
        var p = F.Id("p"); var g = F.Id("G"); var h = F.Id("H");
        return All("p", Nat(), Imp(Call("NatPrime", p),
            Ex("G", Call("FiniteGroup"), Ex("H", Call("FiniteGroup"),
                And(Eq(Call("NatCard", Carrier(g)), new Formula.Power(p, D(6))),
                    And(Eq(Call("NatCard", Carrier(h)), new Formula.Power(p, D(6))),
                        And(Call("Nonempty", Call("GraphIso", Call("commutingGraph", Carrier(g)), Call("commutingGraph", Carrier(h)))),
                            Negate(Call("Isoclinic", Carrier(g), Carrier(h))))))))));
    }
}

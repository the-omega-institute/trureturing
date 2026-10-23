using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeContactIterationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeContactIteration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Earned actual b contacts let all remaining complete stars be grafted sequentially onto the two-star core, producing a Hamilton cycle on the full F2 union.",
        H("Actual Finite Contact Graft Iteration"),
        Blocks(
            Paragraph(Text(
                "PartialDomain(m,k) is the actual CoreDomain together with all complete "
                + "SupplierStar(contactAnchor(j)) for j in Fin(m-2) with j<k. F2Domain(m) is "
                + "PartialDomain(m,m-2), so it includes every tuple "
                + "(1,...,j+1,m,j+2,...,m-1,0) from the concrete remaining family. The induced "
                + "graph has the actual prefix-reversal generators a, b, c; the domain is defined "
                + "by deletion membership rather than by the support of a chosen walk.")),
            Describe.Lean(DescribeId.Create("native-f2-hamiltonian-cycle"),
                DeclarationHandle.Create(Prefix + "native_f2_hamiltonian_cycle"),
                H("All Actual Remaining Contacts Produce a Complete F2 Hamilton Cycle"),
                StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m at least four, there is a genuine Hamilton cycle on the native "
                        + "three-generator graph induced on the independently specified full F2 union. "
                        + "The statement assumes neither a matching nor the occurrence of any contact "
                        + "edge. Those edges are earned along the same cycle construction.")),
                    Paragraph(Text(
                        "Start with the existing actual two-star core Hamilton cycle. Both endpoints "
                        + "of each contact b edge lie in its contact circle, hence in the core. The "
                        + "concrete contact classification excludes that edge from CoreDeletedEdge. "
                        + "Thus the existing core inventory places every pending contact edge in the "
                        + "initial cycle. This establishes the finite induction's edge invariant.")),
                    Paragraph(Text(
                        "At step k, the next complete star meets PartialDomain(m,k) exactly in its "
                        + "contact circle: the core intersection has already been classified, and "
                        + "the earlier contact stars are pairwise disjoint. The pending-edge invariant "
                        + "supplies the actual b edge at index k, so native one-contact E grafting "
                        + "constructs a Hamilton cycle on PartialDomain(m,k+1).")),
                    Paragraph(Text(
                        "Every later contact edge differs from the edge just opened. Equality of "
                        + "undirected edges would identify a vertex from two disjoint complete "
                        + "contact stars. Old-edge retention therefore carries all later contacts "
                        + "into this same new cycle. Iterating through m-2 actual grafts exhausts "
                        + "the finite family and yields the complete F2 witness."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This result constructs the actual finite F2 layer. It does not identify the "
                + "full graph with that layer or prove the later marked-path recombination and "
                + "all-size recursive Hamiltonicity conclusion. An exact arbitrary-edge inventory "
                + "for the whole iterated cycle is a further obligation.")))));

    private static Formula CycleFormula()
    {
        Formula m = F.Id("m"), b = F.Id("base"), w = F.Id("w");
        Formula domain = Call("F2Domain", m), vertices = Call("Vertices", domain);
        Formula cycle = Some("base", vertices, Some("w", Call("Walk", Call("domainGraph", domain), b, b),
            Call("IsHamiltonianCycle", w)));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m), cycle)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}

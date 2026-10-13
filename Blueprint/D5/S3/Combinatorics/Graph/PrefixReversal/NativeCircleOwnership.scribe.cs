using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeCircleOwnershipDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual two T supplier stars intersect in exactly two core circles and their union has a unique complete circle owner.",
        H("Native Circle Ownership"),
        Blocks(
            Paragraph(Text(
                "The ownership argument compares actual tuple cycles. Rotation preserves both cyclic neighbours "
                + "of every label and whole reversal exchanges next with previous. Existing coordinate equivalence "
                + "then proves that two distinct insertion gaps cannot share a complete circle.")),
            Describe.Lean(DescribeId.Create("circle-gap-disjoint"),
                DeclarationHandle.Create(Prefix + "native_circle_gap_disjoint"),
                H("Distinct Insertion Gaps Have Disjoint Circle Domains"),
                StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is an actual support statement for the F2 supplier decomposition. It uses the literal "
                    + "rotation/reversal quotient and does not infer ownership from a chosen path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circle-neighbours"),
                DeclarationHandle.Create(Prefix + "circle_neighbours"),
                H("Circle Ownership Preserves the Unordered Cyclic Neighbours"),
                StatementSource.FromAuthor(NeighbourFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Actual tuple rotations preserve next and previous labels, while whole reversal exchanges "
                    + "them. This invariant is the reusable boundary for cross-supplier ownership."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("t-cross-circle-disjoint"),
                DeclarationHandle.Create(Prefix + "native_t_cross_circle_disjoint"),
                H("The Two Native T Suppliers Have Disjoint Circle Domains"),
                StatementSource.FromAuthor(TCrossFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m at least four, the lower ports a*c*(bc)^i and the upper ports "
                    + "swap(0,last)*a*c*(bc)^j have disjoint complete rotation-and-reversal circle "
                    + "domains. At the label m, the lower neighbours are 1 and m-1, whereas the upper "
                    + "neighbours are j+2 and either 1 or j+1; the unordered-neighbour invariant then "
                    + "gives the arithmetic contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("t-core-intersection"),
                DeclarationHandle.Create(Prefix + "native_t_core_intersection"),
                H("The Two Complete Supplier Stars Intersect Exactly in Their Core Circles"),
                StatementSource.FromAuthor(CoreFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two stars are defined independently by actual deletion of the label in the last position "
                    + "of a*c or swap(0,last)*a*c. Their intersection consists precisely of the complete circles "
                    + "based at the identity and swap(0,last). The two final insertion gaps are computed pointwise; "
                    + "all other shared ownership is excluded by the actual cross-circle theorem. This supplies "
                    + "the two core domains required by the F2 splice, without assuming a path partition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("t-circle-partition"),
                DeclarationHandle.Create(Prefix + "native_t_circle_partition"),
                H("The Full Two-Star Union Has Exactly One Complete Circle Owner"),
                StatementSource.FromAuthor(PartitionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cut-owner index is Fin(m) plus Fin(m-2). Its first family comprises all lower insertion "
                    + "gaps, including the two shared cores; its second family comprises just the upper noncore "
                    + "ports. Every actual vertex in the independently specified union belongs to exactly one "
                    + "complete indexed circle. Full gap exhaustion supplies existence, and the earned core "
                    + "classification and disjointness supply uniqueness. This is a support partition; actual "
                    + "F2 path splicing and the higher marked-path induction remain separate obligations."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), i = F.Id("i"), j = F.Id("j");
        Formula left = Call("gapAnchor", z, i), right = Call("gapAnchor", z, j);
        Formula body = Call("Disjoint", Call("circleDomain", left), Call("circleDomain", right));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("z", Call("Configuration", m), All("i", Call("Fin", m), All("j", Call("Fin", m),
                    Implies(Not(Eq(i, j)), body)))))));
    }

    private static Formula NeighbourFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), v = F.Id("v"), x = F.Id("x");
        Formula same = And(Eq(Call("nextLabel", v, x), Call("nextLabel", z, x)),
            Eq(Call("prevLabel", v, x), Call("prevLabel", z, x)));
        Formula rev = And(Eq(Call("nextLabel", v, x), Call("prevLabel", z, x)),
            Eq(Call("prevLabel", v, x), Call("nextLabel", z, x)));
        Formula fin = Call("Fin", Call("add", m, D(1)));
        return Disp(All("m", Call("Nat"), All("z", Call("Configuration", m),
            All("v", Call("Configuration", m), All("x", fin,
                Implies(Call("Circle", z, v), Or(same, rev)))))));
    }

    private static Formula TCrossFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i"), j = F.Id("j"), v = F.Id("v");
        Formula ac = Call("mul", Call("a", m), Call("c", m));
        Formula bc = Call("mul", Call("b", m), Call("c", m));
        Formula lower(Formula k) => Call("mul", ac, Call("pow", bc, Call("val", k)));
        Formula upper(Formula k) => Call("mul", Call("swap", D(0), Call("last", m)), lower(k));
        Formula lowerDomain = Call("circleDomain", lower(i));
        Formula upperDomain = Call("circleDomain", upper(j));
        Formula body = Call("Disjoint", lowerDomain, upperDomain);
        Formula fin = Call("Fin", Call("sub", m, D(2)));
        Formula sets = All("i", fin, All("j", fin, body));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m), sets)));
    }

    private static Formula CoreFormula()
    {
        Formula m = F.Id("m"), v = F.Id("v");
        Formula ac = Call("mul", Call("a", m), Call("c", m));
        Formula swap = Call("swap", D(0), Call("last", m));
        Formula upper = Call("mul", swap, ac);
        Formula star(Formula z) => Call("Star", Call("apply", z, Call("last", m)),
            Call("residualList", z), v);
        Formula common = And(star(ac), star(upper));
        Formula cores = Or(Call("Circle", D(1), v), Call("Circle", swap, v));
        Formula body = new Formula.Logic(common, FormulaLogicOperator.Iff, cores);
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("v", Call("Configuration", m), body))));
    }

    private static Formula PartitionFormula()
    {
        Formula m = F.Id("m"), v = F.Id("v"), p = F.Id("p"), q = F.Id("q");
        Formula ac = Call("mul", Call("a", m), Call("c", m));
        Formula swap = Call("swap", D(0), Call("last", m));
        Formula upper = Call("mul", swap, ac);
        Formula star(Formula z) => Call("Star", Call("apply", z, Call("last", m)),
            Call("residualList", z), v);
        Formula owners = Call("Sum", Call("Fin", m), Call("Fin", Call("sub", m, D(2))));
        Formula owns(Formula x) => Call("Circle", Call("tCircleAnchor", x), v);
        Formula unique = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("p"),
            owners, And(owns(p), All("q", owners, Implies(owns(q), Eq(q, p)))));
        Formula body = new Formula.Logic(Or(star(ac), star(upper)), FormulaLogicOperator.Iff, unique);
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("v", Call("Configuration", m), body))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Not(Formula x) => new Formula.Not(x);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Or(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Or, r);
}

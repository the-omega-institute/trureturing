using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeCircleOwnershipDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual native circle domains from distinct insertion gaps are disjoint.",
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

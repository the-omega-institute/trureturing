using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CFMPCircularTriangleDiskCoreDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Topology/CFMPCircularTriangleDiskCore";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic triangle-fan seam relation preserves radial size and joins all labelled origins.",
        H("Core invariants of a cyclic triangle fan"),
        Blocks(
            Paragraph(Text(
                "A triangle is a pair of nonnegative real coordinates a,b with a+b at most one. "
                + "The finite fan consists of one copy of this triangle for each i in Fin(n), with n positive. "
                + "The seam generator identifies the edge (t,0) in copy i with the edge (t,0) in the next copy; "
                + "the target is written in the corresponding edge coordinates of the next label. "
                + "The relation used below is exactly the reflexive, symmetric and transitive closure of these generators.")),
            Describe.Lean(DescribeId.Create("radial-size-invariant"),
                DeclarationHandle.Create(Module + ".radialSize_eq_of_seamRel"),
                H("Radial size is constant on generated seam classes"),
                StatementSource.FromAuthor(F.Disp(RadialInvariant())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Radial size is a+b in the triangle component. Each generating seam keeps the same parameter t, "
                    + "so the equality propagates through reflexivity, symmetry and transitivity. This is the invariant "
                    + "needed for a radial map to descend to the quotient. The full complex-valued angular map and its "
                    + "quotient topology are separate obligations and are not asserted here.")))),
            Describe.Lean(DescribeId.Create("origin-step"),
                DeclarationHandle.Create(Module + ".seam_origin_step"),
                H("A generator joins consecutive labelled origins"),
                StatementSource.FromAuthor(F.Disp(OriginStep())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The parameter t=0 is an actual seam generator, so the origin in copy i is related to the origin "
                    + "in the next copy. No kernel of a candidate radial map is used to define this relation.")))),
            Describe.Lean(DescribeId.Create("origin-connectivity"),
                DeclarationHandle.Create(Module + ".seam_origin_all"),
                H("All labelled origins lie in one generated class"),
                StatementSource.FromAuthor(F.Disp(OriginAll())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Finite induction along the labels, with the explicit modulo successor at each step, joins every "
                    + "origin to the origin in copy zero. This proves the central fibre clause of the cyclic fan "
                    + "construction while retaining the generator-defined equivalence relation.")))),
            Describe.Lean(DescribeId.Create("origin-radial-zero"),
                DeclarationHandle.Create(Module + ".seam_origin_radial_zero"),
                H("Every labelled origin has radial size zero"),
                StatementSource.FromAuthor(F.Disp(OriginRadius())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The radial coordinate of each origin representative is exactly zero. Together with origin "
                    + "connectivity and radial invariance, this identifies the distinguished zero-radius class.")))))));

    private static Formula RadialInvariant()
    {
        var n = Id("n");
        return All("n", Call("Nat"),
            All("hn", Positive(n),
                All("x", Call("Fan", n), All("y", Call("Fan", n),
                    Implies(Call("SeamRel", n, Id("hn"), Id("x"), Id("y")),
                        Eq(Call("radialSize", Id("x")), Call("radialSize", Id("y"))))))));
    }

    private static Formula OriginStep()
    {
        var n = Id("n"); var i = Id("i");
        return All("n", Call("Nat"), All("hn", Positive(n), All("i", Call("Fin", n),
            Call("SeamRel", n, Id("hn"), Call("originEdge", i), Call("originEdge", Call("next", Id("hn"), i))))));
    }

    private static Formula OriginAll()
    {
        var n = Id("n");
        return All("n", Call("Nat"), All("hn", Positive(n), All("i", Call("Fin", n),
            Call("SeamRel", n, Id("hn"), Call("originEdge", Call("zeroIndex", Id("hn"))),
                Call("originEdge", Id("i"))))));
    }

    private static Formula OriginRadius()
    {
        var n = Id("n");
        return All("n", Call("Nat"), All("hn", Positive(n), All("i", Call("Fin", n),
            Eq(Call("radialSize", Call("originEdge", Id("i"))), F.D(0)))));
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula Positive(Formula n) => new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, n);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}

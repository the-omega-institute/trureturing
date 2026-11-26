using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MarkedAssemblyFixedPointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MarkedAssemblyFixedPoints.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed assemblies with any finite number of independently transported markers split exactly into fixed and moved blocks.",
        H("Assemblies with a finite marker family"), Blocks(
            Node("fixed_assembly_weight_factorization", "Splitting invariant assemblies",
                Binders(Eqn(Call("fixedSum", V("k"), V("allowed"), V("S"), V("T"), V("g"), V("sign")),
                    Mul(Call("assemblySum", V("k"), V("allowed"), Call("Fix", V("g"), V("S")),
                            Call("Fix", V("g"), V("T")), V("sign")),
                        Call("fixedSum", V("k"), V("allowed"), Call("Moved", V("g"), V("S")),
                            V("T"), V("g"), V("sign")))), true),
                "Let k be any natural number, V and C finite types, and V have decidable equality. " +
                "A block consists of an ordered list of distinct vertices, a color, and a function from Fin k to V. " +
                "An assembly is a finite set of nonempty blocks whose vertex lists partition S; each color satisfies " +
                "allowed(length,color), and every marker coordinate belongs to T. Coordinates may repeat, and T " +
                "is independent of the vertex support S. Its integer weight is the product of sign(color), with " +
                "arbitrary integer signs. The displayed sums range over these actual assemblies. Fix(g,S) and " +
                "Moved(g,S) are the vertices of S fixed and moved by the permutation g. Invariant means stability " +
                "under simultaneous relabeling of the ordered list and every marker, leaving colors unchanged. " +
                "A block containing a fixed vertex must be invariant, because its image shares that vertex. " +
                "The order then fixes each vertex individually, and every marker is fixed. Filtering by fixed " +
                "and moved supports is an equivalence with inverse disjoint union. Its weights multiply. " +
                "The moved blocks retain T; the fixed blocks restrict their markers to Fix(g,T). Empty sets, " +
                "zero markers and all integer color weights are included. No stability premise on S or T is imposed."),
            Node("assembly_weight_point_recursion", "Removing the block at a chosen vertex",
                Binders(All("x", V("V"), Imp(Call("mem", V("x"), V("S")),
                    Eqn(Call("assemblySum", V("k"), V("allowed"), V("S"), V("T"), V("sign")),
                        Call("rootSum", V("k"), V("allowed"), V("S"), V("T"), V("x"), V("sign"))))), false),
                "For every x in S, rootSum sums sign(color(b)) times the assembly sum on S minus the vertices " +
                "of b, with the same T, over all admissible ordered decorated blocks b containing x. " +
                "Coverage and disjointness give exactly one such block in every assembly. Removing and inserting " +
                "this block are inverse operations, and insertion multiplies its color weight into the remaining " +
                "assembly weight. The theorem includes every k and imposes no invariance hypothesis. " +
                "MarkedAssemblyCoefficients uses this recurrence to prove the exponential coefficient formula."))));

    private static Formula Binders(Formula body, bool permutation)
    {
        body = All("sign", Call("Function", V("C"), Z()), body);
        if (permutation) body = All("g", Call("Perm", V("V")), body);
        return All("k", N(), All("V", Call("FiniteTypes"), All("C", Call("FiniteTypes"),
            All("allowed", Call("Predicate", N(), V("C")), All("S", Call("Finset", V("V")),
                All("T", Call("Finset", V("V")), body))))));
    }
    private static DocumentBlock Node(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("marked-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(V(name))) : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
}

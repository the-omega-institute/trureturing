using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FlatBranchDepthCostDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/FlatBranchDepthCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete binary dependency expansions have an exact additive and strict depth cost.",
        H("The length cost of a complete binary dependency tree"),
        Blocks(
            Paragraph(Text("A DependencyTree Q has a labelled root at every leaf or branch, and a branch has two ordered child trees. Complete means that the two children of every branch have the same height. Admissible candidate relations record the positive flat-candidate inequality at every branch; repeated leaves remain repeated occurrences in the leaf sum.")),
            Paragraph(Text("Assume 1 < z(q) for every label and z(q) >= 1 + z(a) + z(b) whenever candidate(q,a,b). Expanding a complete tree gives one unit for every branch and retains every leaf occurrence. A complete tree of height h has 2^h leaves and 2^h-1 branches, so the root is at least (2^h-1) plus the repeated leaf total, and therefore strictly exceeds 2^(h+1)-1.")),
            Paragraph(Text("This formalization is the exact reusable content of CFMP_GEOMETRIC_REALIZATION, Section 46.2. It treats the full-tree hypothesis explicitly and makes no claim that an arbitrary acyclic candidate family admits such a complete expansion.")),
            Describe.Lean(
                DescribeId.Create("full-binary-lower-bound"),
                DeclarationHandle.Create(Prefix + "full_binary_lower_bound"),
                H("Exact additive cost for a complete expansion"),
                StatementSource.FromAuthor(F.Disp(LowerBoundStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction on the tree combines the two child bounds. Equal child heights rewrite the parent height as child height plus one, and the two powers combine with pow_succ. The branch inequality then yields the exact additive lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-binary-strict-bound"),
                DeclarationHandle.Create(Prefix + "full_binary_strict_bound"),
                H("Strict exponential depth cost"),
                StatementSource.FromAuthor(F.Disp(StrictBoundStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact bound is combined with the strict leaf estimate: every one of the 2^h leaf occurrences is greater than one. This gives z(root) > 2^(h+1)-1, with no distinctness requirement on the leaf labels."))),
                DescribeRole.Theorem)
        )));

    private static Formula LowerBoundStatement()
    {
        var q = F.Id("Q");
        var real = F.Id("Real");
        var z = F.Id("z");
        var candidate = F.Id("candidate");
        var tree = F.Id("tree");
        var hpositive = All("q", q, Lt(F.D(1), Apply(z, F.Id("q"))));
        var hstep = All([("q", q), ("a", q), ("b", q)],
            Imp(Apply(candidate, F.Id("q"), F.Id("a"), F.Id("b")),
                Ge(Apply(z, F.Id("q")),
                    Add(F.D(1), Add(Apply(z, F.Id("a")), Apply(z, F.Id("b")))))));
        var assumptions = And(hstep, And(Apply("Complete", tree), Apply("Admissible", candidate, tree)));
        var rhs = Add(Sub(Pow(F.D(2), Apply("height", tree)), F.D(1)), Apply("leafTotal", z, tree));
        return All("Q", F.Id("Type"),
            All("z", Call("Function", q, real),
                All("candidate", Call("Function", q, Call("Function", q, Call("Function", q, F.Id("Prop")))),
                    All("tree", Apply("DependencyTree", q),
                        Imp(And(hpositive, assumptions), Ge(Apply(z, Apply("root", tree)), rhs))))));
    }

    private static Formula StrictBoundStatement()
    {
        var q = F.Id("Q");
        var real = F.Id("Real");
        var z = F.Id("z");
        var candidate = F.Id("candidate");
        var tree = F.Id("tree");
        var hpositive = All("q", q, Lt(F.D(1), Apply(z, F.Id("q"))));
        var hstep = All([("q", q), ("a", q), ("b", q)],
            Imp(Apply(candidate, F.Id("q"), F.Id("a"), F.Id("b")),
                Ge(Apply(z, F.Id("q")),
                    Add(F.D(1), Add(Apply(z, F.Id("a")), Apply(z, F.Id("b")))))));
        var assumptions = And(hstep, And(Apply("Complete", tree), Apply("Admissible", candidate, tree)));
        var lhs = Sub(Pow(F.D(2), Add(Apply("height", tree), F.D(1))), F.D(1));
        return All("Q", F.Id("Type"),
            All("z", Call("Function", q, real),
                All("candidate", Call("Function", q, Call("Function", q, Call("Function", q, F.Id("Prop")))),
                    All("tree", Apply("DependencyTree", q),
                        Imp(And(hpositive, assumptions), Lt(lhs, Apply(z, Apply("root", tree))))))));
    }

    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(name, args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula All((string Name, Formula Type)[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. vars.Select(v => new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Ge(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(left, right);
}

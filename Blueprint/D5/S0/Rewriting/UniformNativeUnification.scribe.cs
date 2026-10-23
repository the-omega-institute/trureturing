using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;
internal sealed class UniformNativeUnificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/UniformNativeUnification.";
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("uniformnativeunification-" + n.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n.Split('.')[^1]), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform computable native unification", H("UniformNativeUnification"), Blocks(
            Paragraph(Text("The finite-tree representation preserves constructor order, equation order, Boolean leaves and every repeated variable occurrence. A list representation of the native substitution preserves each original-key lookup. Fresh insertion composes the new binding into all old values. The bounded evaluator follows the existing native variable, occurs-check, constructor and alias branches. Its mutual simulation preserves the actual native substitution action; no alternative most-general unifier is substituted.")),
            Paragraph(Text("Primitive recursive tree folds compute substitution, variables, branch selection, range checking and output projection. A partial recursive code fixed point implements the bounded mutual evaluator. Fuel induction proves that its code evaluation is total at every fuel. The existing exact finite native simulation supplies termination for the unbounded first-finished search. Partial recursive search and this termination proof establish a total computable solver, with no uniform primitive recursive bound or complexity assertion.")),
            Entry("Code.apply", "Finite composed action", "The finite substitution representation acts by original-key lookup on variables and structurally on Boolean and binary constructors.", DescribeRole.Definition),
            Entry("Code.vars", "Ordered variable occurrences", "The finite list retains all variable occurrences in left-to-right tree order, including repeated names.", DescribeRole.Definition),
            Entry("Code.Represents", "Exact native lookup relation", "For each natural-number ordinal, native lookup equals the native encoding of the finite representation's lookup. Hash-bucket order has no role in this relation.", DescribeRole.Definition),
            Entry("Code.insert", "Composed fresh insertion", "A fresh original binding is inserted after its action has been composed into each prior value. The finite list retains the native first-lookup convention.", DescribeRole.Definition),
            Entry("Code.one", "Coded bounded equation evaluation", "The finite representation follows the existing native one-equation evaluator at identical fuel, retaining equality, both variable orientations, occurs checks, aliases and constructor decomposition.", DescribeRole.Definition),
            Entry("Code.core", "Coded bounded list evaluation", "The finite representation evaluates the ordered equation list at identical fuel and transfers each successful composed substitution to the remaining equations.", DescribeRole.Definition),
            Entry("Code.Matches", "Exact bounded result relation", "Exhaustion matches exhaustion; failure matches the native error branch; success preserves every original-key lookup of the native substitution. Only the outer solver interface discards error payloads.", DescribeRole.Definition),
            Entry("Code.view", "Finite tree case analysis", "The view separates a Boolean or variable leaf from an ordered pair of child trees.", DescribeRole.Definition),
            Entry("computable_F", "Uniform total computability", "The single solver function on all finite Nat-indexed equations is computable. Exact bounded simulation, finite native halting and encoded first-finished search establish this result for arbitrary domain sizes, with no supplied solver or normalization oracle.", DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class InfiniteParityContinuityObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/InfiniteParityContinuityObstruction."
            + "finite_support_parity_has_no_continuous_completion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total parity on finite-support Boolean configurations has no continuous "
            + "completion on the full countable product.",
        H("Infinite Parity Continuity Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-support-parity-has-no-continuous-completion"),
            DeclarationHandle.Create(Declaration),
            H("Finite-support total parity has no continuous completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite set of natural-number coordinates represents a finite "
                        + "prime configuration through the canonical readout map. Its "
                        + "total parity is the Boolean decision of odd support cardinality.")),
                Paragraph(Text(
                    "The initial-segment configurations converge coordinatewise to the "
                        + "all-active path. Continuity into the discrete Boolean space "
                        + "would make their parity eventually constant, while consecutive "
                        + "even and odd prefix lengths always give different values."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula boolean = F.Id("Bool");
        Formula extension = F.Id("extension");
        Formula support = F.Id("support");
        Formula path = Arrow(naturals, boolean);
        Formula extensionType = Arrow(path, boolean);
        Formula finiteSupport = Call("Finset", naturals);
        Formula parity = Call("decide", Call("Odd", Call("card", support)));
        Formula agreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("support", finiteSupport)],
            Equal(Apply(extension, Call("readout", support)), parity));
        Formula proposedCompletion = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("extension", extensionType)],
            And(Call("Continuous", extension), agreement));

        return Disp(new Formula.Not(proposedCompletion));
    }
}

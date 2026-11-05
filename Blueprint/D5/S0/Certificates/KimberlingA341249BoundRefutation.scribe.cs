using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class KimberlingA341249BoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/KimberlingA341249BoundRefutation.";
    private const string SourceDefinition =
        "OEIS A341249, NAME, revision 10 (unpaginated): "
        + "\"a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).\" ";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kimberling2021a341249");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The term n = 2 refutes the upper bound in the OEIS A341249 conjecture.",
        H("Kimberling's OEIS A341249 Bound"),
        Blocks(
            Node("r", "The outer multiplier", Disp(Equal(
                Seq(F.Id("r"), Colon, Reals()), Add(D(2), RootTwo()))),
                SourceDefinition + "The outer multiplier r is a real number.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("s", "The inner multiplier", Disp(Equal(
                Seq(F.Id("s"), Colon, Reals()), RootTwo())),
                SourceDefinition + "The inner multiplier s is a real number.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The nested-floor sequence", SequenceFormula(),
                SourceDefinition + "The index n is natural, and both floors take integer "
                    + "values. Integer and natural values in real products are cast to Real. "
                    + "The source begins at n = 1 with 3, 6, 13, 17; the Lean function "
                    + "also has its formula-defined value at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured two strict bounds", Disp(new Formula.Logic(
                F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody()))),
                "OEIS A341249, COMMENTS, revision 10 (unpaginated): "
                    + "\"Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1.\" "
                    + "The index n ranges over the natural numbers with n at least 1. "
                    + "Both inequalities are strict and are evaluated in Real.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The upper bound fails at n = 2",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "At n = 2, the inner floor is 2 and the outer floor is 6. "
                    + "The difference r*s*2 - a(2) is 4*sqrt(2) - 2, which exceeds 2 "
                    + "because sqrt(2) > 1. Thus the universal conjunction is false.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kimb341249-bound"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a341249-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var inner = Floor(Multiply(F.Id("s"), AsReal(n)));
        return Disp(AllNatural("n", Equal(Call("a", n),
            Floor(Multiply(F.Id("r"), AsReal(inner))))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var difference = Subtract(Multiply(Multiply(F.Id("r"), F.Id("s")),
            AsReal(n)), AsReal(Call("a", n)));
        var bounds = new Formula.Logic(
            Parenthesized(new Formula.Relation(D(1),
                FormulaRelationOperator.LessThan, difference)),
            FormulaLogicOperator.And,
            Parenthesized(new Formula.Relation(difference,
                FormulaRelationOperator.LessThan, D(2))));
        return AllNatural("n", new Formula.Logic(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n),
            FormulaLogicOperator.Implies, Parenthesized(bounds)));
    }

    private static Formula AllNatural(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        Seq(Mathbb, Grp(F.Id("N"))), body);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula RootTwo() => Seq(Sqrt, Grp(D(2)));
    private static Formula Floor(Formula value) => Seq(Lfloor, Sp, value, Rfloor);
    private static Formula AsReal(Formula value) =>
        Parenthesized(Seq(value, Colon, Reals()));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}

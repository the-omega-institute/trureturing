using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroDivisor;

internal sealed class MekeraRankIntegrationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mekerasomeryesil2026matrixarcranks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block ranks characterize ordered arcs in full matrix rings over fields.",
        H("Rank tests for ordered annihilator-digraph arcs"),
        Blocks(
            Describe.Lean(DescribeId.Create("ordered-arc-rank"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration.arc_iff_rank"),
                H("The ordered arc rank criterion"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Mekera, Somer and Yeşil ask in the second paragraph of Section 7 "
                        + "how the arcs of the annihilator digraph of the full matrix ring can be "
                        + "characterized in terms of matrix ranks. Let F be any field, n at least "
                        + "two, and A and B distinct nonzero singular n-by-n matrices over F. "
                        + "Nonzero singular matrices are exactly the vertices of the digraph.")),
                    Paragraph(Text(
                        "Write C = AB. The left witness exists exactly when the rank of C is "
                        + "strictly below both the rank of A and the rank of the horizontal block "
                        + "formed by adjoining the columns of B to C. The right witness exists "
                        + "exactly when the rank of C is strictly below both the rank of B and "
                        + "the rank of the vertical block formed by stacking the rows of A below C. "
                        + "Either witness suffices for the arc from A to B. The reverse arc uses BA "
                        + "with the endpoint roles exchanged.")),
                    Paragraph(Text(
                        "The right witness requires a vector in the kernel of C outside both "
                        + "endpoint kernels. Two proper subspaces cannot cover the kernel of C, "
                        + "even over the binary field. Rank–nullity converts the resulting strict "
                        + "kernel inclusions into the two right-witness inequalities. Transposing "
                        + "and exchanging the endpoints gives the left-witness inequalities."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Par(Formula formula) => Seq(Open, formula, Close);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Then(Formula premise, Formula conclusion) =>
        Seq(premise, Sp, To, Sp, conclusion);
    private static Formula Binder(Formula variable, Formula type) => Seq(variable, Colon, Sp, type);
    private static Formula All(Formula binder, Formula body) =>
        Seq(Forall, Sp, binder, Comma, Sp, body);
    private static Formula Rank(Formula matrix) => Call("rank", matrix);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Statement()
    {
        var field = F.Id("F");
        var n = F.Id("n");
        var a = F.Id("A");
        var b = F.Id("B");
        var product = Multiply(a, b);
        var k = Rank(product);
        var left = And(Lt(k, Rank(a)), Lt(k, Rank(Call("fromCols", product, b))));
        var right = And(Lt(k, Rank(b)), Lt(k, Rank(Call("fromRows", product, a))));
        var criterion = Par(Seq(Call("arc", a, b), Sp, Iff, Sp,
            Par(Seq(Par(left), Sp, Lor, Sp, Par(right)))));
        var singularEndpoint = (Formula matrix) =>
            Par(And(NotEqual(matrix, D(0)), Equal(Call("det", matrix), D(0))));
        var endpoints = All(Binder(Seq(a, Comma, Sp, b), new Formula.Apply(
                new Formula.Subscript(F.Id("M"), n), [field])),
            Then(NotEqual(a, b), Then(singularEndpoint(a), Then(singularEndpoint(b), criterion))));
        var dimension = All(Binder(n, Seq(Mathbb, Grp(F.Id("N")))),
            Then(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n), endpoints));
        return All(Seq(Par(Binder(field, Seq(Operatorname, Grp(F.Id("Type"))))), Sp,
            OpenBracket, Call("Field", field), CloseBracket), dimension);
    }
}

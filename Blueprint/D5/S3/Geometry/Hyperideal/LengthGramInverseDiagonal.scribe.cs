using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramInverseDiagonalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramInverseDiagonal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse of a six-length Lorentz Gram matrix has positive diagonal entries.",
        H("Positive Diagonal of the Inverse Length Gram Matrix"),
        Blocks(
            Paragraph(Text(
                "For six positive lengths, the four by four length Gram matrix has "
                + "a negative determinant in the hyperideal regime. Each diagonal "
                + "cofactor is a three by three Gram determinant with all three "
                + "hyperbolic cosine entries greater than one, hence negative. "
                + "Dividing the negative cofactors by the negative determinant "
                + "gives strict positivity on the diagonal of the inverse.")),
            Describe.Lean(
                DescribeId.Create("length-gram-inverse-diagonal-positive"),
                DeclarationHandle.Create(Prefix + "inverse_diagonal_pos"),
                H("Strict positivity of every inverse diagonal entry"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof expands the four principal adjugate minors using "
                    + "the finite three by three determinant formula. The elementary "
                    + "inequality 1-u squared-v squared-w squared-2uvw < 0 for "
                    + "u,v,w greater than one supplies their signs. Matrix.inv_def "
                    + "then combines a negative determinant with a negative adjugate "
                    + "entry."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var i = F.Id("i");
        var positiveLength = All("k", F.Id("Fin6"), Greater(Call("l", F.Id("k")), F.D(0)));
        var determinantNegative = Less(Call("det", Call("lengthGram", l)), F.D(0));
        var inverseEntry = Call("entry", Call("inv", Call("lengthGram", l)), i, i);
        var conclusion = Greater(inverseEntry, F.D(0));
        return All("l", F.Id("Length6"),
            Impl(positiveLength,
                Impl(determinantNegative,
                    All("i", F.Id("Fin4"), conclusion))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Impl(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}

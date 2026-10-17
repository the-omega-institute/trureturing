using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FaceSignatureBalanceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FaceSignatureBalance.equal_face_counts_iff_opposite_balance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal face signatures characterize opposite-pair balance in a tetrahedral edge coloring.",
        H("Face signatures and opposite-pair balance"),
        Blocks(
            Paragraph(Text("Number the local edges (12,13,14,34,24,23). A Boolean coloring marks "
                + "each local edge as low (true) or high (false). The four faces omit "
                + "vertices 1, 2, 3, 4 "
                + "respectively, and faceLowCount counts the three low edge occurrences "
                + "on each face.")),
            Describe.Lean(
                DescribeId.Create("tetrahedral-face-signature-balance"),
                DeclarationHandle.Create(Declaration),
                H("Equal signatures force opposite edges to agree"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every coloring of all six local edges, the four face "
                        + "counts are pairwise equal exactly when edges 12 and 34, 13 and 24, "
                        + "and 14 and 23 have matching colors. No restriction is placed on "
                        + "the number of low edges.")),
                    Paragraph(Text("The three differences among the four face counts recover "
                        + "the three opposite-pair color differences. Conversely, each face "
                        + "contains exactly one member of each opposite pair. The finite "
                        + "six-color computation establishes both directions.")),
                    Paragraph(Text("This is a local incidence statement. It does not assert "
                        + "that faces have been paired into a manifold or that any geometric "
                        + "edge lengths or angles exist."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var low = F.Id("low");
        var face = F.Id("faceLowCount");
        var fin4 = Call("Fin", F.D(4));
        var fin6 = Call("Fin", F.D(6));
        var colorType = new Formula.TypeArrow(fin6, F.Id("Bool"));
        var i = F.Id("i"); var j = F.Id("j");
        var equalFaces = All([("i", fin4), ("j", fin4)],
            Equal(Apply(face, low, i), Apply(face, low, j)));
        var balanced = And(
            Equal(Apply(low, F.D(0)), Apply(low, F.D(3))),
            Equal(Apply(low, F.D(1)), Apply(low, F.D(4))),
            Equal(Apply(low, F.D(2)), Apply(low, F.D(5))));
        return All([("low", colorType)],
            new Formula.Logic(equalFaces, FormulaLogicOperator.Iff, balanced));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);

    private static Formula And(params Formula[] formulas)
    {
        var result = formulas[^1];
        for (var i = formulas.Length - 2; i >= 0; i--)
            result = new Formula.Logic(formulas[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(F.Id(name), arguments);
}

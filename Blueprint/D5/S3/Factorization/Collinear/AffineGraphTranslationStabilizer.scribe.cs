using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Collinear;

internal sealed class AffineGraphTranslationStabilizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The translation stabilizer of an affine graph is the slope lift of its abscissa stabilizer.",
        H("Affine Graph Translation Stabilizer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affine-graph-translation-stabilizer"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Collinear/AffineGraphTranslationStabilizer.affineGraph_stabilizer_eq_map"),
                H("The graph stabilizer is the slope lift"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Translation by (h,k) sends the graph over X to the graph over h+X with "
                    + "intercept b+k-ah. Equal graphs have equal first-coordinate projections. "
                    + "Since X is nonempty, equality at one abscissa forces k=ah. "
                    + "This argument works over commutative rings with zero divisors."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Statement()
    {
        var r = F.Id("R");
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("X");
        var graph = Call("affineGraph", a, b, x);
        var left = Call("Stab", Call("prod", r, r), graph);
        var right = Call("map", Call("Stab", r, x), Call("slopeHom", a));
        return new Formula.Logic(
            Call("Nonempty", x),
            FormulaLogicOperator.Implies,
            new Formula.Relation(left, FormulaRelationOperator.Equal, right));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RussoDyeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle equality and norm scale in complex C-star algebras.",
        H("RussoDye"), Blocks(
            Describe.Lean(DescribeId.Create("russodye-closedconvexhull-unitary"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RussoDye.closedConvexHull_unitary"),
                H("closedConvexHull unitary"),
                StatementSource.FromAuthor(All("A",Ty,Inst(Call("CStarAlgebra",X("A")),Equal(Call("closedConvexHull",R,F.Seq(Parenthesized(Call("unitary",X("A"))),F.Colon,Call("Set",X("A")))),App(Q("Metric","closedBall"),F.Seq(N(0),F.Colon,X("A")),N(1)))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/suzuki2026russodye")),
                Blocks(Paragraph(Text("The Russo-Dye theorem identifies the closed real convex hull of the unitaries with the closed unit ball of a unital complex C-star algebra, including the zero algebra."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Ty => Call("Type");
    private static Formula R => Call("Real");
    private static Formula N(long value) => new Formula.Number(value);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => F.Seq(F.Open, f, F.Close);
    private static Formula Q(string owner, string name) => F.Seq(F.Operatorname, F.Grp(X(owner)), F.Dot, F.Operatorname, F.Grp(X(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => F.Seq(F.OpenBracket, type, F.CloseBracket, F.Sp, body);
}

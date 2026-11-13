using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class FixedDiagonalDeterminantDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string names, Formula type, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse())
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
        return body;
    }
    private static Formula Instance(string name, params Formula[] xs) =>
        Seq(OpenBracket, Call(name, xs), CloseBracket, Sp);
    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Seq(Open, x, Close), FormulaLogicOperator.Implies, Seq(Open, y, Close));
    private static Formula Context(Formula body, bool nontrivial) => All("K Omega", V("Type"), Seq(
        Instance("Field", V("K")), Instance("Fintype", V("Omega")),
        Instance("DecidableEq", V("Omega")),
        nontrivial ? Instance("Nontrivial", V("Omega")) : Sp,
        All("N", Call("Matrix", V("Omega"), V("Omega"), V("K")), body)));
    private static Formula Row => Call("rowMatrix", V("N"));
    private static Formula RowDefinition => Context(Equal(Row,
        new Formula.Binary(D(1), FormulaBinaryOperator.Add,
            new Formula.Binary(Call("diagonal", Call("X", V("Omega"))), FormulaBinaryOperator.Multiply,
                Call("map", Call("coefficientEmbedding", V("K"), V("Omega")), V("N"))))), false);
    private static Formula Irreducibility => Context(Imp(
        All("i j", V("Omega"), Call("ReflTransGen", Call("nonzeroSupport", V("N")), V("i"), V("j"))),
        Call("Irreducible", Call("det", Row))), true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Irreducibility for the row-parameter determinant of a fixed matrix.",
        H("Fixed coefficients and diagonal parameters"), Blocks(
            Paragraph(Text("K is any field and Omega is a finite label type. Every entry of N is fixed. "
                + "The variables are indexed only by Omega; neither matrix entries nor support edges "
                + "are independent variables. C is the coefficient embedding and X(Omega) is the "
                + "family sending each label i to its polynomial variable X(i).")),
            Describe.Lean(DescribeId.Create("row-matrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.rowMatrix"),
                H("Row-parameter matrix"), StatementSource.FromAuthor(Disp(RowDefinition)),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The matrix is I plus diag(x) times N. Its determinant has constant coefficient one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row-determinant-irreducible"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.row_determinant_irreducible"),
                H("Irreducibility from the actual directed support"),
                StatementSource.FromAuthor(Disp(Irreducibility)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("nonzeroSupport(N) has an edge from i to j exactly when N(i,j) is nonzero. "
                    + "ReflTransGen permits any finite directed path, including length zero. "
                    + "Nontrivial Omega means at least two labels. No order, positivity, characteristic, "
                    + "generic position or restriction on the coefficients is assumed.")),
                    Paragraph(Text("Differentiate the matrix-adjugate identity entrywise. A zero adjugate "
                    + "entry forces the product of the two adjugate entries on every two-step route to vanish. "
                    + "Evaluation at x=0 gives the identity adjugate; differentiating there shows that "
                    + "every nonzero off-diagonal coefficient gives a nonzero adjugate entry. Induction "
                    + "along a directed path proves all required adjugate entries are nonzero. "
                    + "The adjugate column with its own row removed is independent of that row parameter. "
                    + "This identifies each determinant derivative and makes every two-parameter Rayleigh "
                    + "difference nonzero. The determinant is multiaffine, so factors would have disjoint "
                    + "variable sets; parameters selected from opposite nonconstant factors would have "
                    + "zero Rayleigh difference, a contradiction.")),
                    Paragraph(Text("The fixed-matrix irreducibility criterion is classical; compare "
                    + "Al Ahmadieh, The Fiber of the principal minor map, arXiv:2309.00806v2, "
                    + "Lemmas 2.2, 4.2 and 5.1. This proof supplies its row-scaled form directly. "
                    + "It does not supply the diagonal-plus-N statement, a Laurent inversion equivalence, "
                    + "or an identification with the original multiplication obstruction polynomial."))),
                DescribeRole.Theorem))));
}

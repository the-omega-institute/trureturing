using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class FinchBalancedZerofreeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/finch2026smallinverses");

    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Name(name), arguments);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp,
            Parenthesized(body));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Int() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Index(Formula n) => Call("Fin", n);
    private static Formula MatrixType(Formula n) => Call("Matrix", Index(n), Index(n), Int());
    private static Formula IntegerMatrix(Formula n) => Call("IntegerMatrix", n);
    private static Formula Inverse(Formula matrix) => new Formula.Power(matrix, Seq(Minus, D(1)));
    private static Formula Nonzero(Formula n, Formula matrix) => All("i", Index(n), All("j", Index(n),
        Ne(App(matrix, X("i"), X("j")), D(0))));
    private static Formula Maximum(Formula n, Formula matrix)
    {
        var pairs = Seq(Index(n), Sp, Times, Sp, Index(n));
        var entries = Parenthesized(Seq(Qualified("Finset", "univ"), Sp, Colon, Sp,
            Call("Finset", pairs)));
        var i = Seq(X("ij"), Dot, D(1));
        var j = Seq(X("ij"), Dot, D(2));
        var value = App(Qualified("Int", "natAbs"), App(matrix, i, j));
        var function = Parenthesized(Seq(Name("fun"), Sp, X("ij"), Sp, Mapsto, Sp, value));
        return App(Qualified("Finset", "sup"), entries, function);
    }
    private static Formula IntegerMatrixBody() =>
        All("n", Nat(), Eq(IntegerMatrix(X("n")), MatrixType(X("n"))));
    private static Formula MaxAbsEntryBody() =>
        All("n", Nat(), All("M", IntegerMatrix(X("n")),
            Eq(Call("maxAbsEntry", X("M")), Maximum(X("n"), X("M")))));
    private static Formula UnimodularBody() =>
        All("n", Nat(), All("M", IntegerMatrix(X("n")),
            Eq(Call("Unimodular", X("M")),
                Call("IsUnit", App(Qualified("Matrix", "det"), X("M"))))));
    private static Formula AlphaBody() =>
        All("n", Nat(), All("M", IntegerMatrix(X("n")),
            Eq(Call("alpha", X("M")), Call("maxAbsEntry", X("M")))));
    private static Formula BetaBody() =>
        All("n", Nat(), All("M", IntegerMatrix(X("n")),
            Eq(Call("beta", X("M")), Maximum(X("n"), Inverse(X("M"))))));
    private static Formula ZerofreeBody() =>
        All("n", Nat(), All("M", IntegerMatrix(X("n")),
            Eq(Call("Zerofree", X("M")),
                And(Nonzero(X("n"), X("M")), Nonzero(X("n"), Inverse(X("M")))))));
    private static Formula ClaimBody()
    {
        var matrix = X("M");
        return All("M", IntegerMatrix(D(6)), Imp(Call("Unimodular", matrix),
            Imp(Call("Zerofree", matrix),
                Imp(Eq(Call("alpha", matrix), D(3)),
                    Imp(Eq(Call("beta", matrix), D(3)), Name("False"))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit integer matrix refutes Finch's order-six zerofree conjecture.",
        H("An order-six unimodular zerofree matrix with both maxima three"), Blocks(
            Describe.Lean(DescribeId.Create("integer-matrix"), DeclarationHandle.Create(Prefix + "IntegerMatrix"),
                H("Integer matrices"), StatementSource.FromAuthor(Disp(IntegerMatrixBody())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The source defines “an n×n integer matrix M” with indices 0 through n−1. The carrier is Matrix (Fin n) (Fin n) ℤ."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("max-abs-entry"), DeclarationHandle.Create(Prefix + "maxAbsEntry"),
                H("Maximum absolute entry"), StatementSource.FromAuthor(Disp(MaxAbsEntryBody())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The source uses the maximum absolute entry of M; the displayed finite supremum applies Int.natAbs to all coordinate pairs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unimodular"), DeclarationHandle.Create(Prefix + "Unimodular"),
                H("Unimodular matrices"), StatementSource.FromAuthor(Disp(UnimodularBody())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("An n×n integer matrix M with determinant ±1 is called unimodular."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("alpha"), DeclarationHandle.Create(Prefix + "alpha"),
                H("The source's alpha"), StatementSource.FromAuthor(Disp(AlphaBody())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The source sets α=‖M‖, the maximum absolute entry of M."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("beta"), DeclarationHandle.Create(Prefix + "beta"),
                H("The source's beta"), StatementSource.FromAuthor(Disp(BetaBody())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The source sets β=‖M⁻¹‖, the maximum absolute entry of M⁻¹."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zerofree"), DeclarationHandle.Create(Prefix + "Zerofree"),
                H("Zerofree matrices"), StatementSource.FromAuthor(Disp(ZerofreeBody())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The source calls M zerofree if none of the entries in M and none of the entries in M⁻¹ are zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Finch's Conjecture 4"),
                StatementSource.FromAuthor(Disp(Iff(Name("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("Conjecture 4, printed and PDF page 7: “No 6×6 matrices exist that are tied to α=β=3.”")),
                    Paragraph(Text("Introduction, printed pages 1–2: “An n×n integer matrix M with determinant ±1 is called unimodular. Let α=‖M‖ and β=‖M⁻¹‖, the maximum absolute entry of M and M⁻¹, respectively.”")),
                    Paragraph(Text("The same introduction states: “The matrix M is called zerofree if none of the entries in M and none of the entries in M⁻¹ are zero. (Involving both matrices in this definition is somewhat unorthodox.) Our interest is in unimodular zerofree matrices for which both α and β are small.”")),
                    Paragraph(Text("Here M ranges over all six by six integer matrices. The named predicates and maxima are the definitions displayed above; the inverse is Mathlib's nonsingular matrix inverse."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Conjecture 4 is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Take the integer matrix whose rows are (3,2,2,2,2,2), (2,3,2,2,2,2), (2,2,3,2,2,2), (2,2,2,1,2,2), (2,2,2,2,1,2), and (2,2,2,2,2,1). Its integral inverse has rows (-1,-2,-2,2,2,2), (-2,-1,-2,2,2,2), (-2,-2,-1,2,2,2), (2,2,2,-3,-2,-2), (2,2,2,-2,-3,-2), and (2,2,2,-2,-2,-3). Their product is the identity. Mathlib's right-inverse and determinant-unit theorems identify this inverse and establish unimodularity. Every entry of both matrices is nonzero and both finite absolute maxima are three.")),
                    Paragraph(Text("The cancellation between three positive and three negative diagonal signs gives the displayed small integral inverse. The theorem establishes the single order-six counterexample. A symbolic family in every positive even dimension, exhaustive orbit classification, the separate case α=β=2, and odd-dimensional nonexistence statements remain separate questions. The source's subsequent discussion uses no theorem conditional on Conjecture 4."))), DescribeRole.Theorem))));
}

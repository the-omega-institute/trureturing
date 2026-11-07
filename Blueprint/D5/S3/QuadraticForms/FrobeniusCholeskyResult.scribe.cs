using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class FrobeniusCholeskyResultDocument : IScribeDocumentDefinition
{
    private const string Note = "D5/L/QuadraticForms/wuzhou2026singularcholesky";
    private const string Module = "D5/S3/QuadraticForms/FrobeniusCholeskyResult";
    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Apply(Formula function, params Formula[] args) => Seq(function,
        Parenthesized(Seq([.. args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, Sp, arg })])));
    private static Formula Q(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula App(string name, params Formula[] args) => Apply(Name(name), args);
    private static Formula Typed(string name, Formula type) => Parenthesized(Seq(X(name), Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Member(Formula left, Formula right) => Seq(left, Sp, InMacro, Sp, right);
    private static Formula Imp(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Rightarrow, Sp, Parenthesized(right));
    private static Formula And(params Formula[] clauses) => Seq([.. clauses.SelectMany((clause, i) =>
        i == 0 ? new[] { Parenthesized(clause) } : new[] { Sp, Land, Sp, Parenthesized(clause) })]);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula FinN => App("Fin", X("n"));
    private static Formula Mat(Formula entries) => App("Matrix", FinN, FinN, entries);
    private static Formula Fiber(string name) => App(name, X("F"), X("n"));
    private static Formula Map(Formula value) => Apply(Q("Matrix", "map"), X("p"),
        Apply(Q("Recipe", "eval"), value));
    private static Formula Frob => App("frobenius", X("F"), D(2));
    private static Formula MatrixMap(Formula value) => Apply(Q("Matrix", "map"), value, Frob);
    private static Formula Rank(Formula value) => Apply(Q("Matrix", "rank"), value);

    private static Formula ClaimBody()
    {
        var bijection = Apply(Q("Set", "BijOn"), Parenthesized(Seq(Name("fun"), Sp,
            Typed("X", Mat(X("F"))), Sp, Mapsto, Sp, Map(X("X")))), Fiber("B"), Fiber("C"));
        var ranks = All("X", Mat(X("F")), Imp(Member(X("X"), Fiber("B")),
            Eqn(Rank(Map(X("X"))), Rank(X("X")))));
        var frobenius = All("X", Mat(X("F")), Imp(Member(X("X"), Fiber("B")),
            Eqn(Map(MatrixMap(X("X"))), MatrixMap(Map(X("X"))))));
        Formula body = Imp(Eqn(Apply(Q("Fintype", "card"), X("F")),
            new Formula.Power(D(2), X("e"))), And(bijection, ranks, frobenius));
        body = Instance(App("CharP", X("F"), D(2)), body);
        body = Instance(App("DecidableEq", X("F")), body);
        body = Instance(App("Fintype", X("F")), body);
        body = Instance(App("Field", X("F")), body);
        body = All("F", Name("Type"), body);
        body = Ex("p", Mat(App("Recipe", X("n"))), body);
        body = All("n", Nat, body);
        body = Imp(Seq(D(1), Sp, Le, Sp, X("e")), body);
        return All("e", Nat, body);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite arithmetic recipes give rank-preserving Frobenius-equivariant bijections between upper triangular square-zero matrices and zero Gram roots.",
        H("Frobenius-equivariant Cholesky bijections"),
        Blocks(
            Describe.Lean(DescribeId.Create("frobenius-cholesky-claim"),
                DeclarationHandle.Create(Module + ".claim"), H("The finite-field question"),
                StatementSource.FromAuthor(Disp(Eqn(Name("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Wu and Zhou, Singular Cholesky Fibers over Finite Fields, arXiv:2609.00533v1, Section 8(iv), p. 43: “Over "), Math(new Formula.Subscript(Seq(Mathbb, Grp(X("F"))), new Formula.Power(D(2), X("e")))), Text(", find a version of the rank-preserving bijection that is Frobenius equivariant and avoids the RREF–lexicographic choice. This would strengthen the present flag-compatible construction without changing its rank behavior.” Here B(F,n) consists of upper triangular X with X * X = 0, and C(F,n) consists of upper triangular U with transpose(U) * U = 0. Fin n indexes both rows and columns; n = 0 includes the empty matrix. A single matrix p of Recipe n works over every field presentation with the specified cardinality. Frobenius acts entrywise by x mapped to x squared."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("frobenius-cholesky-result"),
                DeclarationHandle.Create(Module + ".result"), H("Uniform rank-preserving arithmetic construction"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("The proof selects nonzero minors using only coordinate indices and zero tests. Free-coordinate kernel vectors extend independent image columns to adapted kernel frames. Coordinate transport between the two frames is bijective and preserves membership in the old image.")),
                    Paragraph(Text("The recursion transports the final column and makes the final diagonal its coordinate sum. In characteristic two the square of that sum equals the sum of coordinate squares. This gives the zero Gram equation and uniqueness of the final diagonal. Membership of the new column in the old image determines the rank increase on both sides.")),
                    Paragraph(Text("The arithmetic recipe contains no field-element ordering or enumeration. The supporting construction works over every characteristic-two field. Arbitrary coordinate-change naturality and a separately assembled theorem for all field embeddings and leading-principal truncations remain additional questions."))),
                DescribeRole.Theorem))));
}

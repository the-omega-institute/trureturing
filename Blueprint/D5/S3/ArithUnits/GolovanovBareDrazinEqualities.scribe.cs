using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class GolovanovBareDrazinEqualitiesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/GolovanovBareDrazinEqualities.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/golovanov2026spectralcoincidence");

    private static readonly Formula R = F.Id("R");
    private static readonly Formula A = F.Id("a");
    private static readonly Formula B = F.Id("b");
    private static readonly Formula C = F.Id("c");
    private static readonly Formula U = F.Id("u");
    private static readonly Formula V = F.Id("v");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");
    private static readonly Formula P = F.Id("p");
    private static readonly Formula CoreC = F.Id("r");
    private static readonly Formula Z = F.Id("z");
    private static readonly Formula RemA = new Formula.Subscript(F.Id("n"), A);
    private static readonly Formula RemC = new Formula.Subscript(F.Id("n"), C);
    private static readonly Formula T = F.Id("t");
    private static readonly Formula Residue = F.Id("P");
    private static readonly Formula Hx = new Formula.Subscript(F.Id("h"), X);
    private static readonly Formula Ht = new Formula.Subscript(F.Id("h"), T);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three tests characterize the bare Drazin sum equality in a unital associative ring.",
        H("Bare finite Drazin equalities"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-drazin"),
                DeclarationHandle.Create(Prefix + "FD"), H("The finite Drazin relation"),
                StatementSource.FromAuthor(Disp(FiniteDrazinFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The finite Drazin relation requires an outer inverse, commutation with the "
                    + "input, and nilpotence of the remainder. Nilpotence means that some "
                    + "natural power is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("drazin-inverse"),
                DeclarationHandle.Create(Prefix + "drazin"), H("The finite Drazin inverse"),
                StatementSource.FromAuthor(Disp(
                    Seq(Forall, Sp, Ring(), Sp, Binder(X, R), Sp, Binder(Hx, Witness(X)), Comma, Sp,
                        Equal(Apply("drazin", X, Hx), Inverse(X))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "An existence proof supplies a finite Drazin witness. Any two witnesses "
                    + "coincide. A common positive power absorbs both core idempotents and "
                    + "can be multiplied by the same powers of the candidate inverses to "
                    + "identify the cores and then the inverses."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-tests"),
                DeclarationHandle.Create(Prefix + "result"), H("Golovanov's Problem 10.1"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The two unit equations identify b as the inverse of a + c. The input "
                        + "witnesses u and v are the finite Drazin inverses of a and c. The "
                        + "equivalence applies to every unital associative ring, including "
                        + "the zero ring, and allows different input core idempotents.")),
                    Paragraph(Text(
                        "Put s = u + v and use t = a b c = c b a. Expand ts as tu + tv, "
                        + "using c b a for t in tu and a b c for t in tv, to get ts = p + a b z. "
                        + "Expand st as ut + vt, using a b c for t in ut and c b a for t in vt, "
                        + "to get st = p + z b a.")),
                    Paragraph(Text(
                        "The outer inverse defect sts − s equals the negative of zbz. The "
                        + "remainder t − (ts)t equals P by multiplying the two complementary "
                        + "core terms of 1 − ts by the appropriate ordered expression for t. "
                        + "These identities translate commutation, the outer inverse equation, "
                        + "and nilpotence into the three tests."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("golovanov-2026-bare-drazin-equalities-problem-10-1"),
                    ResolutionKind.Proved)))));

    private static Formula FiniteDrazinFormula() =>
        Seq(Forall, Sp, Ring(), Sp, Binder(Seq(X, Comma, Y), R), Comma, Sp,
            Apply("FD", X, Y), Sp, Iff, Sp,
            Paren(Seq(Equal(Product(Y, X, Y), Y), Sp, Land, Sp,
                Equal(Product(X, Y), Product(Y, X)), Sp, Land, Sp,
                Apply("IsNilpotent", Subtract(X, Product(X, Y, X))))));

    private static Formula ResultFormula() =>
        Seq(Forall, Sp, Ring(), Sp, Binder(Seq(A, Comma, C, Comma, U, Comma, V, Comma, B), R), Comma, Sp,
            Equal(Product(Paren(Seq(A, Plus, C)), B), Num(1)), Sp, To, Sp,
            Equal(Product(B, Paren(Seq(A, Plus, C))), Num(1)), Sp, To, Sp,
            Apply("FD", A, U), Sp, To, Sp, Apply("FD", C, V), Sp, To, Sp,
            Let(P, Product(A, U)), Let(CoreC, Product(C, V)), Let(Z, Subtract(CoreC, P)),
            Let(RemA, Subtract(A, Product(P, A))), Let(RemC, Subtract(C, Product(CoreC, C))),
            Let(T, Subtract(A, Product(A, B, A))),
            Let(Residue, Seq(Product(C, B, RemA, B, C), Sp, Plus, Sp, Product(A, B, RemC, B, A))),
            Paren(Seq(Exists, Sp, Binder(Ht, Witness(T)), Comma, Sp,
                Equal(Inverse(T), Seq(Inverse(A), Sp, Plus, Sp, Inverse(C))))), Sp, Iff, Sp,
            Paren(Seq(Equal(Product(A, B, Z), Product(Z, B, A)), Sp, Land, Sp,
                Equal(Product(Z, B, Z), Num(0)), Sp, Land, Sp, Apply("IsNilpotent", Residue))));

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula Paren(Formula body) => Seq(Open, body, Close);
    private static Formula Binder(Formula name, Formula type) => Paren(Seq(name, Colon, Sp, type));
    private static Formula Ring() => Seq(Binder(R, Name("Type")), Sp, OpenBracket, Apply("Ring", R), CloseBracket);
    private static Formula Inverse(Formula value) => new Formula.Power(value, F.Id("D"));
    private static Formula Product(params Formula[] factors) => Seq(factors);
    private static Formula Let(Formula lhs, Formula rhs) =>
        Seq(Name("let"), Sp, lhs, Sp, Colon, Eq, Sp, rhs, Comma, Sp);
    private static Formula Witness(Formula x) => Seq(Exists, Sp, Binder(Y, R), Comma, Sp, Apply("FD", x, Y));
}

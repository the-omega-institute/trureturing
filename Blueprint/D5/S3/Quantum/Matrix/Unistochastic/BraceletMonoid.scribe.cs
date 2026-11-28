using System;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Unistochastic;

internal sealed class BraceletMonoidDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/Unistochastic/BraceletMonoid.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/rajchelkorzekwapuchalazyczkowski2021birkhoff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bracelet matrices contain the identity and are closed under ordinary multiplication in every finite dimension.",
        H("The bracelet matrices form a monoid"), Blocks(
            Paragraph(Text(
                "For each natural number d, matrices have real entries and both indices range over Fin d. "
                    + "The predicate IsBracelet is the existing interface from CirculantBraceletNonUnistochastic. "
                    + "It includes entrywise nonnegativity, unit row and column sums, and the column and row "
                    + "bracelet inequalities for distinct indices. The theorem keeps that predicate unchanged.")),
            Describe.Lean(
                DescribeId.Create("bracelet-monoid"), DeclarationHandle.Create(Prefix + "bracelet_monoid"),
                H("Identity and product closure"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "This is the all-finite-dimensional form of Conjecture 9. The identity clauses use "
                            + "disjoint supports in distinct rows and columns. For products, the column family "
                            + "is transported through a rectangular preservation lemma. A pair of nonnegative "
                            + "input weights is lifted to orthogonal complex amplitudes by a polygon construction. "
                            + "The weighted Lagrange identity records the output overlap as the Euclidean norm "
                            + "of one weighted inner-product coordinate and ordered minor coordinates. Unit column "
                            + "sums cancel the inner-product coordinates, the input bracelet bounds control the minors, "
                            + "and the Euclidean triangle inequality gives the output inequality. Applying the same "
                            + "argument to transposed factors supplies the row family.")),
                    Paragraph(Text(
                        "The statement includes d = 0 because Fin d is allowed to be empty. In that dimension the "
                            + "distinct-index families are vacuous. No positivity, field, rectangular, or complex "
                            + "matrix conclusion is added to the real square-matrix interface."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rajchel-korzekwa-puchala-zyczkowski-2021-bracelet-monoid"),
                    ResolutionKind.Proved))
        )));

    private static Formula Statement()
    {
        Formula d = V("d"), a = V("A"), b = V("B");
        Formula matrices = MatrixType(d);
        Func<Formula, Formula> bracelet = x =>
            App(Qualified("CirculantBraceletNonUnistochastic", "IsBracelet"), x);
        Formula identity = Typed(D(1), matrices);
        Formula product = Multiply(a, b);
        return All("d", Naturals(), And(
            bracelet(identity),
            All("A", matrices, All("B", matrices,
                Imp(bracelet(a), Imp(bracelet(b), bracelet(product)))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula MatrixType(Formula d) => Call("Matrix", Fin(d), Fin(d), Reals());
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        App(V(name), arguments);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

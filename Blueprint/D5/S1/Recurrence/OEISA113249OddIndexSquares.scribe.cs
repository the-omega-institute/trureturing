using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class OEISA113249OddIndexSquaresDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/OEISA113249OddIndexSquares.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dement2005a113249");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every odd-index term in Dement's fourth-order integer family is a square.",
        H("Odd-index squares in the A113249 family"),
        Blocks(
            Paragraph(Text(
                "The parameter m and index n are natural numbers, including zero. "
                + "The values of a are integers, and every displayed cast (m : ℤ) "
                + "is the natural parameter regarded as an integer. Index arithmetic "
                + "is natural arithmetic; value arithmetic is integer arithmetic. "
                + "IsSquare is Mathlib's predicate asserting the existence of an "
                + "integer r with the value equal to r*r.")),
            Node("a", "The fourth-order family", SequenceFormula(),
                "OEIS A113249, unpaginated Name (%N): \"Corresponds to m = 3 in a "
                + "family of 4th-order linear recurrence sequences given by a(m,n) = "
                + "m^4*a(n-4) + (2*m)^2*a(n-3) - 4*a(n-1), a(m,0) = -1, "
                + "a(m,1) = 4, a(m,2) = -13 + 6*(m-1) + 3*(m-1)^2, "
                + "a(m,3) = (-8+m^2)^2.\" The family parameter is m : ℕ, the "
                + "sequence index is n : ℕ, and the values lie in ℤ. The recurrence "
                + "is displayed at n+4. In the initial value at index 2, m-1 is "
                + "integer subtraction, also at m=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Dement's conjecture",
                Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "OEIS A113249, unpaginated Comments (%C): \"Conjecture: "
                + "a(m, 2*n+1) is a perfect square for all m, n.\" The variables "
                + "m and n range over ℕ, including zero, and IsSquare is taken "
                + "over ℤ. The source lists family parameters m=0 through m=10; "
                + "the proposition quantifies over every natural m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All odd-index terms are squares", Disp(ClaimBody()),
                "The auxiliary integer sequence starts at 2 and m²-8 and satisfies "
                + "b(n+2)=-4b(n+1)-m²b(n). The subsequence a(m,2n+1) and the "
                + "squares of these auxiliary terms satisfy the same order-three "
                + "recurrence, with coefficients 16-m², m⁴-16m², and m⁶. They "
                + "agree at n=0, 1, 2. Induction preserves this window of three "
                + "identities, so each auxiliary term is an integer square root "
                + "of the corresponding odd-index term. The argument includes "
                + "every natural m without a nonzero or distinct-root hypothesis.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a113249-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula SequenceFormula()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var z = Parenthesized(Seq(m, Colon, Sp, Integers()));
        var difference = Parenthesized(Subtract(z, D(1)));
        return Disp(new Formula.Aligned([
            Seq(Named("a"), Colon, Sp, Naturals(), Sp, To, Sp,
                Naturals(), Sp, To, Sp, Integers()),
            All("m", Naturals(), Equal(Call("a", m, D(0)), new Formula.Negate(D(1)))),
            All("m", Naturals(), Equal(Call("a", m, D(1)), D(4))),
            All("m", Naturals(), Equal(Call("a", m, D(2)),
                Add(Add(new Formula.Negate(D(1, 3)), Multiply(D(6), difference)),
                    Multiply(D(3), Power(difference, D(2)))))),
            All("m", Naturals(), Equal(Call("a", m, D(3)),
                Power(Parenthesized(Add(new Formula.Negate(D(8)), Power(z, D(2)))), D(2)))),
            All("m", Naturals(), All("n", Naturals(),
                Equal(Call("a", m, Add(n, D(4))),
                    Subtract(Add(Multiply(Power(z, D(4)), Call("a", m, n)),
                        Multiply(Power(Parenthesized(Multiply(D(2), z)), D(2)),
                            Call("a", m, Add(n, D(1))))),
                        Multiply(D(4), Call("a", m, Add(n, D(3)))))))),
        ]));
    }

    private static Formula ClaimBody() => All("m", Naturals(), All("n", Naturals(),
        Call("IsSquare", Call("a", F.Id("m"), Add(Multiply(D(2), F.Id("n")), D(1))))));

    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
}

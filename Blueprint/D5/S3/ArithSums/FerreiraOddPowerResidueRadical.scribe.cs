using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class FerreiraOddPowerResidueRadicalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/FerreiraOddPowerResidueRadical.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/ferreira2026a399232");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-power residue sum determines the radical of its odd modulus.",
        H("Ferreira's odd-power residue radical identity"),
        Blocks(
            Paragraph(Text("The index n is natural. Remainders in the finite sum are "
                + "the least nonnegative natural remainders. The radical is the product "
                + "of distinct prime divisors. The deficit and quotient are rational.")),
            Node("a", "The literal residue sum", SumFormula(),
                "Sum k to the power 4n+1 modulo 2n+1 over every integer k from "
                + "one through 4n+2, including both complete blocks of residues.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Positive deficit and radical quotient", ResultFormula(),
                "Set m=2n+1 and r=rad(m). Divisibility of x to the power 4n+1 by m "
                + "is equivalent to divisibility of x by r. Thus exactly m/r members "
                + "of a complete block have zero remainder. Negation pairs each "
                + "nonzero remainder with its complement in m. The two literal "
                + "blocks therefore satisfy a(n)+m(m/r)=m squared. The signed "
                + "rational deficit is m(m/r)>0, and r(m/r)=m gives the quotient.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a399232-radical-identity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("a399232-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula BoundN() => Seq(Forall, Sp, F.Id("n"), Colon, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp);

    private static Formula SumFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var m = Par(Add(Mul(D(2), n), D(1)));
        var e = Par(Add(Mul(D(4), n), D(1)));
        var upper = Add(Mul(D(4), n), D(2));
        var summand = new Formula.Modulo(new Formula.Power(k, e), m);
        return Disp(Seq(BoundN(), Call("a", n), Sp, Eq, Sp, Sum, Underscore,
            Grp(Seq(k, Eq, D(1))), Caret, Grp(upper), Sp, Par(summand)));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var m = Par(Add(Mul(D(2), n), D(1)));
        var square = new Formula.Power(m, D(2));
        var deficit = Sub(square, Call("a", n));
        return Disp(Seq(BoundN(), Par(Seq(D(1), Sp, Le, Sp, n)), Sp, Implies, Sp,
            Par(Seq(D(0), Sp, Lt, Sp, deficit)), Sp, Land, Sp,
            Call("rad", m), Sp, Eq, Sp, new Formula.Fraction(square, deficit)));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaIntegralCompositionDivTenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2016a277403");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational exponential generating series of A277403 has integral coefficients divisible by ten above index two.",
        H("Hanna's integral composition equation modulo ten"),
        Blocks(
            Paragraph(Text("Exponential coefficients are eCoeff(A,n)=n! times the ordinary coefficient of A. "
                + "The zero integration constant and A(0)=0 agree with the displayed example in OEIS A277403. "
                + "All series are formal power series over the rationals.")),
            Describe.Lean(DescribeId.Create("hanna-solution"),
                DeclarationHandle.Create(Prefix + "IsSolution"), H("The source equation"),
                StatementSource.FromAuthor(Disp(All("A", Series(), All("G", Series(),
                    Iff(Call("IsSolution", F.Id("A"), F.Id("G")), SolutionBody()))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("OEIS A277403, NAME and FORMULA fields, revision #21 (no page number): "
                    + "\"E.g.f. satisfies: A(x - Integral A(x) dx) = x + Integral A(x) dx.\" "
                    + "\"Let G(x) = Integral A(x) dx, then e.g.f. A(x) also satisfies:\" "
                    + "Here A and G are rational formal series; G has zero constant coefficient and derivative A. "
                    + "The displayed example begins x + 2*x^2/2! + 10*x^3/3!."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hanna-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The divisibility assertion"),
                StatementSource.FromAuthor(Disp(Iff(F.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("OEIS A277403, sole COMMENTS conjecture, revision #21 (no page number): "
                    + "\"a(n) is divisible by 10 for n>2 (conjecture).\" "
                    + "The offset is one. The first conjunct asserts integrality at every positive index; "
                    + "the second asserts divisibility at every index greater than two. "
                    + "Integers are explicitly cast into the rationals in both conclusions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hanna-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Divisibility at every index above two"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The coefficient equation is triangular with leading coefficient one. "
                    + "It constructs an integral sequence and proves uniqueness over every commutative ring. "
                    + "Encoding that sequence produces a rational solution of the source equation, "
                    + "so the solution class is nonempty. For P=X+X^2 and J=X^2/2+X^3/3, "
                    + "the complete residual P(X-J)-X-J has exponential coefficients -10,-10,40,80 "
                    + "in degrees three through six and zero elsewhere. Thus P solves the coefficient "
                    + "equation modulo ten. Uniqueness identifies its residues with those of the integral sequence. "
                    + "Reduction acts on integral coefficient sequences and requires no factorial inverses modulo ten."))),
                DescribeRole.Theorem))));

    private static Formula SolutionBody()
    {
        var a = F.Id("A");
        var g = F.Id("G");
        var x = F.Id("X");
        return And(Equal(Call(Qualified("PowerSeries", "constantCoeff"), a), D(0)),
            And(Equal(Call(Qualified("PowerSeries", "constantCoeff"), g), D(0)),
                And(Equal(Call(Qualified("PowerSeries", "derivative"), g), a),
                    Equal(Call(Qualified("PowerSeries", "subst"), Subtract(x, g), a), Add(x, g)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var coefficient = Call("eCoeff", F.Id("A"), n);
        var integral = All("n", Naturals(), Imp(LessEqual(D(1), n),
            Ex("a", Integers(), Equal(coefficient, Cast(F.Id("a"), Rationals())))));
        var divisible = All("n", Naturals(), Imp(Less(D(2), n),
            Ex("k", Integers(), Equal(coefficient,
                Cast(Cast(Multiply(D(1, 0), F.Id("k")), Integers()), Rationals())))));
        return All("A", Series(), All("G", Series(),
            Imp(Call("IsSolution", F.Id("A"), F.Id("G")), And(integral, divisible))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

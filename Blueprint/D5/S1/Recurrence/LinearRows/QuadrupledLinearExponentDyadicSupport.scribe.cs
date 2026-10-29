using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.LinearRows;

internal sealed class QuadrupledLinearExponentDyadicSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2026a397594");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer source series exists for OEIS A397594, and every source series has Hanna's dyadic-neighbor odd support.",
        H("Hanna's Quadrupled Linear Rows and Dyadic Parity"),
        Blocks(
            Paragraph(Text("The ordinary formal series has a(n)=PowerSeries.coeff n A, "
                + "with index zero and a(0)=1. Rational rescaling substitutes X/m after "
                + "mapping each integer coefficient to Q. All powers are formal-series "
                + "products. Subtraction between natural indices is truncated natural "
                + "subtraction; no analytic convergence is required.")),
            Describe.Lean(
                DescribeId.Create("hanna397594-source"),
                DeclarationHandle.Create(Prefix + "IsSourceSeries"),
                H("The rational-rescaling source equation"),
                StatementSource.FromAuthor(SourceDefinition()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("OEIS A397594 revision 15, NAME and FORMULA (1), "
                    + "without pagination: \"G.f. A(x) such that the sum of the first n "
                    + "coefficients in A(x/n)^n equals 4^(n-1) for n >= 1.\" "
                    + "\"(1) 4^(n-1) = Sum_{k=0..n-1} [x^k] A(x/n)^n for n >= 1.\" "
                    + "The natural m below is the source's n, and j is its k. "
                    + "Finset.range m contains exactly j=0 through m-1. The equation "
                    + "is in Q, with A in PowerSeries Z and constant coefficient one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hanna397594-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Integer existence and the parity assertion"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("OEIS A397594 revision 15, COMMENTS, without pagination: "
                    + "\"Conjecture: for n > 3, a(n) is odd iff n is of the form 2^k-1 "
                    + "or 2^k+1 (k > 1).\" Here a(n)=PowerSeries.coeff n A, n and k "
                    + "are natural numbers, and Odd applies to an integer coefficient. "
                    + "Existence of an integer source series is included, and the "
                    + "equivalence quantifies over every source series."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hanna397594-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Hanna's parity assertion proved"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Clearing the rescaling denominators gives the integer "
                    + "row equation. Triangular normalization has forcing "
                    + "4^n(n+1)^(n-1) in positive degree. Coefficientwise iteration "
                    + "constructs an integer solution. The forcing vanishes modulo two, "
                    + "so normalized uniqueness and the homogeneous dyadic-support "
                    + "theorem give the parity equivalence for every source solution. "
                    + "The assertion concerns the parameter four; the entire parameter "
                    + "triangle and the source's reversion identities are separate questions."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanna397594"),
                    ResolutionKind.Proved)))));

    private static Formula SourceDefinition()
    {
        var a = F.Id("A");
        var m = F.Id("m");
        var j = F.Id("j");
        var rationalMap = Call(Qualified("Int", "castRingHom"), Rationals());
        var rationalImage = Call(Qualified("PowerSeries", "map"), rationalMap, a);
        var inverse = new Formula.Power(Cast(m, Rationals()), Seq(Minus, D(1)));
        var scaled = Call(Qualified("PowerSeries", "rescale"), inverse, rationalImage);
        var sum = Seq(new Formula.Subscript(Sum,
            new Formula.Relation(j, FormulaRelationOperator.MemberOf,
                Call(Qualified("Finset", "range"), m))), Sp,
            Coeff(j, new Formula.Power(Parenthesized(scaled), m)));
        var rows = All("m", Naturals(), ImpliesFormula(Less(D(0), m),
            Equal(sum, new Formula.Power(Cast(D(4), Rationals()), Sub(m, D(1))))));
        var body = And(Equal(Call(Qualified("PowerSeries", "constantCoeff"), a), D(1)), rows);
        return Disp(All("A", SeriesType(), new Formula.Logic(
            SourceAt(a), FormulaLogicOperator.Iff, Parenthesized(body))));
    }

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var k = F.Id("k");
        var power = new Formula.Power(D(2), k);
        var support = ExistsFormula("k", Naturals(), And(Less(D(1), k),
            new Formula.Logic(Equal(n, Sub(power, D(1))), FormulaLogicOperator.Or,
                Equal(n, Add(power, D(1))))));
        var parity = All("A", SeriesType(), ImpliesFormula(SourceAt(a),
            All("n", Naturals(), ImpliesFormula(Less(D(3), n),
                new Formula.Logic(Call("Odd", Coeff(n, a)), FormulaLogicOperator.Iff,
                    Parenthesized(support))))));
        return And(ExistsFormula("A", SeriesType(), SourceAt(a)), parity);
    }

    private static Formula SourceAt(Formula a) => Call("IsSourceSeries", a);
    private static Formula Coeff(Formula n, Formula a) => Call(Qualified("PowerSeries", "coeff"), n, a);
    private static Formula SeriesType() => Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Z"))));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Call(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsFormula(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

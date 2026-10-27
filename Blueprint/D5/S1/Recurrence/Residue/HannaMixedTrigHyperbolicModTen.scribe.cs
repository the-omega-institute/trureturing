using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaMixedTrigHyperbolicModTenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/HannaMixedTrigHyperbolicModTen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2013a227051");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-index factorial-normalized coefficient of Hanna's reciprocal is an integer congruent to three modulo ten.",
        H("Hanna's Mixed Trigonometric and Hyperbolic Reciprocal"),
        Blocks(
            Paragraph(Text("OEIS A227051, revision 10, NAME (no numbered page): "
                + "E.g.f.: 1/(cos(x) - sin(x)*sinh(x)), omitting the zero-valued coefficients of odd powers of x. "
                + "All series below lie in PowerSeries over the rationals. "
                + "Mathlib's PowerSeries.cos and PowerSeries.sin are rational Taylor series. "
                + "The natural index n selects degree 2*n. The existing eCoeff(f,k) is "
                + "k! times coeff(k,f), so a(n) retains the source's factorial normalization. "
                + "The notation val(z) in the formula is the coercion from integers to rationals.")),
            Node("sinhSeries", "The hyperbolic sine Taylor series", SinhFormula(),
                "The odd Taylor coefficient is the inverse of the factorial; every even coefficient is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("denominator", "The mixed denominator", Disp(Equal(Named("denominator"),
                Subtract(App(Qualified("PowerSeries", "cos"), Rationals()),
                    Multiply(App(Qualified("PowerSeries", "sin"), Rationals()), Named("sinhSeries"))))),
                "OEIS A227051, revision 10, NAME (no numbered page): "
                + "E.g.f.: 1/(cos(x) - sin(x)*sinh(x)), omitting the zero-valued coefficients of odd powers of x.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The reciprocal series", Disp(Equal(Named("A"),
                new Formula.Power(Named("denominator"), DMinusOne()))),
                "The formal inverse is taken over the rationals. The denominator has constant coefficient one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The even factorial-normalized coefficients", Disp(Seq(Bound("n", Naturals()),
                Equal(Call("a", F.Id("n")), App(Qualified("IntegralEGFComposition", "eCoeff"),
                    Named("A"), Multiply(D(2), F.Id("n")))))),
                "OEIS A227051, revision 10, PARI program (no numbered page): "
                + "(PARI) {a(n)=local(X=x+x*O(x^(2*n))); (2*n)!*polcoeff(1/(cos(X) - sin(X)*sinh(X)), 2*n)} "
                + "Thus n=0 selects the constant coefficient, and no odd-degree coefficient is included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's congruence assertion", Disp(new Formula.Logic(Named("claim"),
                FormulaLogicOperator.Iff, Parenthesized(ClaimBody()))),
                "OEIS A227051, revision 10, first FORMULA (no numbered page), verbatim: "
                + "a(n) == 3 (mod 10) for n>0 (conjecture). "
                + "The natural index satisfies 1<=n. An integer z equals a(n) in the rationals "
                + "and satisfies the integer congruence, so integrality is part of the assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The congruence at every positive index", Disp(ClaimBody()),
                "The denominator coefficients are d(2r)=1 and d(2r+1)=-1-2*(-4)^r. "
                + "The binomial product equation identifies the rational coefficients with an integer recurrence. "
                + "Triangular uniqueness identifies its inverse modulo two with 1,1,1,... "
                + "and its inverse modulo five with 1,3,3,... . Coprimality of two and five "
                + "gives the stated congruence. The calculation uses finite coefficient identities "
                + "and does not invert factorials in a residue field.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("hanna-a227051-" + (name == "A" ? "reciprocal" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula DMinusOne() => Seq(Minus, D(1));

    private static Formula SinhFormula() => Disp(Equal(Named("sinhSeries"),
        App(Qualified("PowerSeries", "mk"), Seq(Named("fun"), Sp,
            Parenthesized(Seq(F.Id("m"), Colon, Naturals())), Sp, Mapsto, Sp,
            Call("ite", Call("Even", F.Id("m")), D(0),
                new Formula.Power(Parenthesized(Seq(
                    App(Qualified("Nat", "factorial"), F.Id("m")), Colon, Rationals())), DMinusOne()))))));

    private static Formula ClaimBody() => Seq(Bound("n", Naturals()),
        new Formula.Logic(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            FormulaLogicOperator.Implies, Seq(Exists, Sp, F.Id("z"), Colon, Integers(), Comma, Sp,
                new Formula.Logic(Equal(Call("a", F.Id("n")), Call("val", F.Id("z"))),
                    FormulaLogicOperator.And, App(Qualified("Int", "ModEq"), D(1, 0), F.Id("z"), D(3))))));
}

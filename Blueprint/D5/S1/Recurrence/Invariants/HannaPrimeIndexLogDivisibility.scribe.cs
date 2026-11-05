using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaPrimeIndexLogDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaPrimeIndexLogDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a381355");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral source series exists and its logarithmic derivative satisfies Hanna's prime divisibility.",
        H("Hanna's OEIS A381355 prime-index divisibility"),
        Blocks(
            Paragraph(Text("The prime function is PrimePowerShiftLogDerivative.prime, the one-based "
                + "prime schedule with prime(1)=2. The series have rational coefficients. Natural "
                + "subtraction specifies the coefficient index n-1, and the asserted indices satisfy n>1. "
                + "The inverse is formal power-series inversion. Casts to the rationals are displayed explicitly.")),
            Node("IsSourceSeries", "The source equations", SourceDefinition(),
                "OEIS A381353 NAME: \"G.f. A(x) satisfies [x^n] A(x)^prime(n) = 0 for n > 1.\" "
                + "Its PROGRAM initializes \"my(A=[1,1])\", fixing coefficients zero and one to one. "
                + "These are the NAME and PROGRAM sections of revision 19; the entry has no page numbers. "
                + "The source's A(x) is denoted F here, and coeff extracts a coefficient indexed from zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sourceTerm", "The sequence and its index", TermDefinition(),
                "OEIS A381355 NAME: \"G.f. A(x) = x*F'(x)/F(x) where F(x) is the g.f. of A381353 "
                + "that satisfies [x^n] F(x)^prime(n) = 0 for n > 1.\" This is the NAME section of "
                + "revision 13, without page numbers. The entry's offset is one: its nth term is "
                + "coeff (n-1) (derivative F * F⁻¹). The definition is total at zero, which is outside "
                + "the asserted range.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's conjecture with source existence", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A381355 COMMENTS: \"Conjecture: a(n) is divisible by prime(n) for n > 1.\" "
                + "This is the COMMENTS section of revision 13, without page numbers. The first conjunct "
                + "asserts existence of a rational source series. The second ranges over every such series. "
                + "An integer z witnesses divisibility inside the rationals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Existence and prime divisibility", Disp(ClaimBody()),
                "Reduction modulo a prime makes all positive coefficients below that prime vanish in "
                + "the corresponding power. Exact integral corrections therefore construct a source series. "
                + "The coefficient change under a power gives uniqueness among rational source series. "
                + "The formal derivative identity makes the relevant product coefficient zero over the "
                + "integers; cancellation of the nonzero prime and reduction modulo that prime isolate "
                + "the coefficient of the logarithmic derivative.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hanna381355-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Prime(Formula n) =>
        new Formula.Apply(Qualified("PrimePowerShiftLogDerivative", "prime"), [n]);
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Rationals()));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesFormula(Formula premise, Formula body) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(body));
    private static Formula GreaterThanOne(Formula n) => Seq(D(1), Sp, Lt, Sp, n);
    private static Formula Inverse(Formula series) => new Formula.Power(Parenthesized(series), Seq(Minus, D(1)));

    private static Formula SourceDefinition()
    {
        Formula f = F.Id("F");
        Formula n = F.Id("n");
        return Disp(All("F", Series(), Seq(Call("IsSourceSeries", f), Sp, Iff, Sp,
            And(Equal(Call("coeff", D(0), f), D(1)),
                And(Equal(Call("coeff", D(1), f), D(1)),
                    All("n", Naturals(), ImpliesFormula(GreaterThanOne(n),
                        Equal(Call("coeff", n, new Formula.Power(f, Prime(n))), D(0)))))))));
    }

    private static Formula TermDefinition()
    {
        Formula f = F.Id("F");
        Formula n = F.Id("n");
        return Disp(All("F", Series(), All("n", Naturals(),
            Equal(Call("sourceTerm", f, n), Call("coeff", Subtract(n, D(1)),
                Parenthesized(Multiply(Call("derivative", f), Inverse(f))))))));
    }

    private static Formula ClaimBody()
    {
        Formula f = F.Id("F");
        Formula n = F.Id("n");
        Formula z = F.Id("z");
        return And(Some("F", Series(), Call("IsSourceSeries", f)),
            All("F", Series(), ImpliesFormula(Call("IsSourceSeries", f),
                All("n", Naturals(), ImpliesFormula(GreaterThanOne(n),
                    Some("z", Integers(), Equal(Call("sourceTerm", f, n),
                        Multiply(Cast(Prime(n)), Cast(z)))))))));
    }
}

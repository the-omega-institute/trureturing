using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaBilateralReversionParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a379202");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairing bilateral Laurent summands proves the evenness conjecture for OEIS A379202.",
        H("Hanna's Bilateral Reversion Parity"),
        Blocks(
            Paragraph(Text("P. D. Hanna's OEIS A379202 states: \"G.f. A(x) satisfies "
                + "1/x = Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 2)^(n+1).\" "
                + "Its Comments section states: \"Conjecture: a(n) is even for n > 1.\" "
                + "The entry has offset 1 and begins 1, 4, 20, 122, 850. "
                + "OEIS entries have named sections rather than page numbers.")),
            Paragraph(Text("Integer powers and inversion take place in LaurentSeries over the rationals. "
                + "The natural index j selects the Laurent coefficient j-1. For A=X+… the "
                + "nonnegative summand n has order at least n, and the summand -m has order "
                + "m²-2m. Thus the finite window in bilateralSum contains every contributing "
                + "summand. The type annotations on casts distinguish natural and integer indices.")),
            Node("term", "The Laurent summand", TermFormula(),
                "The summand in the entry's Name section, quoted above, uses the integer "
                + "exponents n and n+1 without replacing inversion by power-series division.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bilateralSum", "The bilateral Laurent sum", BilateralFormula(),
                "The Name section's \"Sum_{n=-oo..+oo}\" is interpreted coefficientwise. "
                + "Multiplication by single(-1,1) shifts the constructed series down one degree. "
                + "The coefficient of degree j-1 is summed over integers from -j-2 to j+2, inclusive.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsGF", "The generating equation", IsGFFormula(),
                "\"G.f. A(x) satisfies 1/x = Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 2)^(n+1).\" "
                + "This is the Name section of A379202. Offset 1 and the first entry 1 give "
                + "constantCoeff A=0 and coeff 1 A=1. The coefficient a(n) is coeff n A.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The evenness conjecture", Disp(Equivalent(F.Id("claim"), ClaimBody())),
                "\"Conjecture: a(n) is even for n > 1.\" (A379202, Comments section; no page number.) "
                + "The formula asserts existence of the rational generating series and, for every "
                + "such series and every natural n>1, an integer coefficient z that is even. "
                + "Even is Mathlib's integer parity predicate.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the evenness conjecture", Disp(ClaimBody()),
                "Isolate the summand n=-1. Pair n=k with n=-k-2 for every natural k. "
                + "The latter folds to A^(k(k+2)) times the (k+1)st power of the inverse of "
                + "1+2A^(k+2). Both members reduce to A^(k(k+2)) modulo two, so each pair "
                + "vanishes. The normalized integer series T therefore reduces to 1. "
                + "The series B=X/T has zero constant coefficient and linear coefficient 1; "
                + "its integral compositional inverse reduces to X modulo two. Laurent-series "
                + "normalization identifies every solution of the displayed equation with this "
                + "inverse over the rationals, proving integrality and evenness for n>1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a379202-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Laurent() => Call("LaurentSeries", Rationals());
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Bound(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Equivalent(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Iff, Sp, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula CastInteger(Formula value) => Typed(value, Integers());
    private static Formula Negated(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Inverse(Formula value) => Power(Parenthesized(value), Seq(Minus, D(1)));
    private static Formula Coeff(Formula index, Formula series) =>
        App(Q("PowerSeries", "coeff"), index, series);

    private static Formula TermFormula()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var an = Power(Typed(a, Laurent()), n);
        return Disp(Bound(Forall, "A", Series(), Bound(Forall, "n", Integers(),
            Equal(Call("term", a, n), Multiply(an,
                Power(Parenthesized(Add(an, D(2))), Add(n, D(1))))))));
    }

    private static Formula BilateralFormula()
    {
        var a = F.Id("A");
        var j = F.Id("j");
        var n = F.Id("n");
        var ji = CastInteger(j);
        var window = App(Q("Finset", "Icc"), Subtract(Negated(ji), D(2)), Add(ji, D(2)));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(n, Sp, InMacro, Sp, window)), Sp,
            App(Q("HahnSeries", "coeff"), Call("term", a, n), Subtract(ji, D(1))));
        var coefficients = Seq(Operatorname, Grp(F.Id("fun")), Sp, Typed(j, Naturals()), Sp, Mapsto, Sp, sum);
        var ordinary = App(Q("PowerSeries", "mk"), Parenthesized(coefficients));
        var embedded = App(Q("HahnSeries", "ofPowerSeries"), Integers(), Rationals(), ordinary);
        return Disp(Bound(Forall, "A", Series(), Equal(Call("bilateralSum", a),
            Multiply(App(Q("HahnSeries", "single"), Typed(Negated(D(1)), Integers()),
                Typed(D(1), Rationals())), embedded))));
    }

    private static Formula IsGFFormula()
    {
        var a = F.Id("A");
        var body = Conjunction(Equal(App(Q("PowerSeries", "constantCoeff"), a), D(0)),
            Conjunction(Equal(Coeff(D(1), a), D(1)),
                Equal(Inverse(Typed(Typed(F.Id("X"), Series()), Laurent())),
                    Call("bilateralSum", a))));
        return Disp(Bound(Forall, "A", Series(), Equivalent(Call("IsGF", a), body)));
    }

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var z = F.Id("z");
        var exists = Bound(Exists, "A", Series(), Call("IsGF", a));
        var coefficients = Bound(Forall, "n", Naturals(),
            Implication(new Formula.Relation(D(1), FormulaRelationOperator.LessThan, n),
                Bound(Exists, "z", Integers(), Conjunction(Equal(Coeff(n, a), Typed(z, Rationals())),
                    Call("Even", z)))));
        return Conjunction(exists, Bound(Forall, "A", Series(),
            Implication(Call("IsGF", a), coefficients)));
    }
}

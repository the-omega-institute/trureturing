using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TebniA350759PrimeCongruencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/tebni2022a350759");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both prime congruences for Tebni's OEIS A350759 sequence.",
        H("Tebni's A350759 prime congruences"),
        Blocks(
            Paragraph(Text("The formal series have rational coefficients. Natural indices start at zero, "
                + "and the sequence values are integers. PowerSeries.log over Q is the series for "
                + "log(1+X); PowerSeries.subst takes the inner series first and the outer series second. "
                + "Integer congruence is Int.ModEq. The prime p=2 is included.")),
            Node("sourceSeries", "The published exponential generating function", SourceFormula(),
                "OEIS A350759, revision 17, FORMULA (unpaginated): "
                + "\"E.g.f.: exp(-1 + (1 + x)*(1 - log(1 + x))).\" "
                + "The displayed substitution is the formal exponential at exactly this exponent.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSequence", "Integer sequences with the source generating function", SequenceFormula(),
                "OEIS A350759, revision 17, FORMULA (unpaginated): "
                + "\"E.g.f.: exp(-1 + (1 + x)*(1 - log(1 + x))).\" "
                + "For a natural-indexed integer sequence a, the existing HannaLogarithmicPowerClosure.egf "
                + "has degree-n coefficient (a(n):Q)/n!; its equality with sourceSeries defines IsSourceSequence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The two COMMENTS assertions", Equal(V("claim"), Parenthesized(ClaimBody())),
                "OEIS A350759, revision 17, COMMENTS (unpaginated): "
                + "\"Conjectures: For all p prime, (a(p) + a(p+1) - 2) == 0 (mod p),\" "
                + "\"a(p+1) == 1 (mod ((p+1)*p)).\" "
                + "The second line inherits the prime quantifier. The formula also asserts existence "
                + "of an integer sequence with the source EGF and covers every sequence with that EGF. "
                + "Subtraction takes place in Z; the product (p+1)*p is formed in N and then cast to Z.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both prime congruences hold", ClaimBody(),
                "The rising-factorial expansion gives an integer factorial-scaled coefficient of the "
                + "form 1+n*z at every index n. The index-zero expansion term is one; each other term "
                + "is a multiple of n. The source differential equation gives an EGF convolution. "
                + "Interior prime binomial coefficients vanish modulo p, and Wilson's theorem settles "
                + "the endpoint, including a separate p=2 case. Combining the residues modulo p and "
                + "p+1 proves the product congruence. Hanna's expansion in OEIS A176118 is prior art.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("tebni350759-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula SourceFormula()
    {
        var x = V("X");
        var exponent = Add(Seq(Minus, D(1)), Mul(Parenthesized(Add(D(1), x)),
            Parenthesized(Sub(D(1), Qualified("PowerSeries", "log", Q())))));
        return Equal(V("sourceSeries"), Qualified("PowerSeries", "subst", exponent,
            Qualified("PowerSeries", "exp", Q())));
    }

    private static Formula SequenceFormula()
    {
        var a = V("a");
        var coefficients = Lambda("n", N(), Cast(Apply(a, V("n")), Q()));
        return All("a", Arrow(N(), Z()), Equal(Call("IsSourceSequence", a),
            Parenthesized(Equal(Qualified("HannaLogarithmicPowerClosure", "egf", coefficients), V("sourceSeries")))));
    }

    private static Formula ClaimBody()
    {
        var a = V("a"); var p = V("p");
        var successor = Add(p, D(1));
        var first = Qualified("Int", "ModEq", Cast(p, Z()),
            Sub(Add(Apply(a, p), Apply(a, successor)), D(2)), D(0));
        var second = Qualified("Int", "ModEq", Cast(Mul(Parenthesized(successor), p), Z()),
            Apply(a, successor), D(1));
        return And(Ex("a", Arrow(N(), Z()), Call("IsSourceSequence", a)),
            All("a", Arrow(N(), Z()), Imp(Call("IsSourceSequence", a),
                All("p", N(), Imp(Qualified("Nat", "Prime", p), And(first, second))))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class SecondOrderStirlingTransformDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/parisse2024hypersequences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A factorial-Stirling identity holds for every complex sequence satisfying a second-order linear recurrence, including zero parameters and every nonnegative offset.",
        H("The complete second-order factorial-Stirling transform"),
        Blocks(Describe.Lean(
            DescribeId.Create("second-order-stirling-transform"),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/SecondOrderStirlingTransform.result"),
            H("The uniform recurrence identity"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "This is a direct formal polynomial derivation of an all-parameter consequence of classical Stirling and geometric-polynomial identities. Kargin's equation (21) gives the reflection including degree zero. Zeitlin's Theorem 9, equations (4.21) and (4.23), provides the real nonzero-parameter antecedent under the correction on page 182; Kellner's Corollary 3.3 gives the positive-degree polynomial symmetry. The exact normalizations and scope restrictions are recorded in the cited note. No priority claim is made for this sum or its zero-parameter extension.")),
                Paragraph(Text(
                "Here S(n,k) is Nat.stirlingSecond n k. Each factorial-Stirling coefficient is computed in Nat before casting to Complex. A range ending at ell+1 contains precisely 0 through ell; subtraction in the exponent is natural subtraction. The two initial values of u are arbitrary. In particular q=0 imposes no equation between u(0) and u(1). Both sides at ell=0 equal u(c), including c=0 and c=1.")),
                Paragraph(Text(
                "Write Q for the existing ordinary factorial-Stirling row polynomial and H for the shifted row with coefficients m! S(ell+1,m+1). Their differential recurrences prove H(-1-X)=(-1)^ell Q(X) for every degree. Homogenization supplies the powers of q without division. Pair a polynomial with u by summing its coefficients against u(j+c). The recurrence makes this pairing vanish on every multiple of X squared minus p X minus q. The difference-of-powers identity then replaces (q+p X) raised to m by X raised to 2m inside the pairing, yielding both finite sums. This argument retains zero parameters, repeated roots, zero initial data and nonnegative offsets without an inverse shift."))),
            DescribeRole.Theorem)), []));

    private static Formula SeqType() => new Formula.TypeArrow(Naturals(), Complexes());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Sum(Formula m, Formula bound, Formula body) =>
        Seq(F.Sum, Underscore, Grp(m, Sp, InMacro, Sp, Call("range", bound)), Sp, Par(body));

    private static Formula Statement()
    {
        Formula p = F.Id("p"), q = F.Id("q"), u = F.Id("u"), n = F.Id("n"),
            ell = F.Id("ell"), c = F.Id("c"), m = F.Id("m");
        var recurrence = All("n", Naturals(), Eq(Call("u", Add(n, D(2))),
            Add(Mul(p, Call("u", Add(n, D(1)))), Mul(q, Call("u", n)))));
        Formula Weight(Formula row, Formula col) => Par(Seq(
            Par(Mul(Call("factorial", m), Call("S", row, col))), Sp, Colon, Sp, Complexes()));
        var left = Sum(m, Add(ell, D(1)),
            Mul(Mul(Mul(Pow(Seq(Minus, D(1)), m), Weight(Add(ell, D(1)), Add(m, D(1)))),
                Pow(q, Sub(ell, m))), Call("u", Add(Mul(D(2), m), c))));
        var right = Mul(Pow(Seq(Minus, D(1)), ell), Sum(m, Add(ell, D(1)),
            Mul(Mul(Mul(Weight(ell, m), Pow(p, m)), Pow(q, Sub(ell, m))),
                Call("u", Add(m, c)))));
        return Disp(All("p", Complexes(), All("q", Complexes(),
            All("ell", Naturals(), All("c", Naturals(), All("u", SeqType(),
            new Formula.Logic(Par(recurrence), FormulaLogicOperator.Implies,
                Par(Eq(left, right)))))))));
    }
}

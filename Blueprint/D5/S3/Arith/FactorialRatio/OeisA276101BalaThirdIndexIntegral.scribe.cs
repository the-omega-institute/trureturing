using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class OeisA276101BalaThirdIndexIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/bala2016integerfactorials");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala A276101 integrality.", H("Bala A276101: integrality at every natural index"), Blocks(
            Node("a", All("n", N(), Eq(Call("a" ,V("n")), Div(Mul(Cast(App(Q("Nat", "factorial") ,Mul(D(1,0), V("n"))), R()), App(Q("Real", "Gamma") ,Add(Div(Cast(V("n"), R()), D(3)), D(1)))), Mul(Mul(Cast(App(Q("Nat", "factorial") ,Mul(D(5), V("n"))), R()), App(Q("Real", "Gamma") ,Add(Div(Mul(D(1,0), Cast(V("n"), R())), D(3)), D(1)))), Cast(App(Q("Nat", "factorial") ,Mul(D(2), V("n"))), R()))))),
                "OEIS A276101, NAME (unpaginated): \"a(n) = (10*n)!*(n/3)!/((5*n)!*(10*n/3)!*(2*n)!).\" Bala, page 1: \"throughout these notes x! is shorthand for Γ(x + 1)\". Natural factorials are cast to the reals.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A276101, COMMENTS (unpaginated): \"This is only conjecturally an integer sequence.\" Bala, page 5: \"are also integral for n ≥ 0.\" Naturals include zero, and integrality means equality to the real cast of an integer.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Parameters", All("d", N(), All("M", N(), All("B", N(), All("C", N(), All("L", N(), Eq(Call("Parameters" ,V("d"), V("M"), V("B"), V("C"), V("L")), Parenthesized(Or(And(Eq(V("d"), D(3)), And(Eq(V("M"), D(1,0)), And(Eq(V("B"), D(5)), And(Eq(V("C"), D(2)), Eq(V("L"), D(3)))))), And(Eq(V("d"), D(5)), And(Eq(V("M"), D(6)), And(Eq(V("B"), D(3)), And(Eq(V("C"), D(2)), Eq(V("L"), D(1)))))))))))))),
                "The two parameter systems for the third-index and fifth-index Gamma ratios.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("progression", All("d", N(), All("L", N(), All("n", N(), Eq(Call("progression" ,V("d"), V("L"), V("n")), RangeProd(Mul(V("L"), V("n")), Add(V("n"), Mul(V("d"), Add(V("k"), D(1))))))))),
                "The product of n+d(k+1) over k in Finset.range (Ln), with the empty product equal to one.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("progression_ne_zero", All("d", N(), All("L", N(), All("n", N(), Impl(Lt(D(0), V("d")), NotEq(Call("progression" ,V("d"), V("L"), V("n")), D(0)))))),
                "Every factor of the progression is positive when d is positive.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("nonmultiple_dvd", All("d", N(), All("M", N(), All("B", N(), All("C", N(), All("L", N(), All("n", N(), Impl(Call("Parameters" ,V("d"), V("M"), V("B"), V("C"), V("L")), Impl(Not(Dvd(V("d"), V("n"))), Dvd(Mul(Mul(App(Q("Nat", "factorial") ,Mul(V("B"), V("n"))), App(Q("Nat", "factorial") ,Mul(V("C"), V("n")))), Call("progression" ,V("d"), V("L"), V("n"))), App(Q("Nat", "factorial") ,Mul(V("M"), V("n")))))))))))),
                "For either parameter system, if d does not divide n, the product of the two denominator factorials and the progression divides the numerator factorial.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("gamma_ratio", All("d", N(), All("L", N(), All("n", N(), Impl(Lt(D(0), V("d")), Eq(Div(App(Q("Real", "Gamma") ,Add(Div(Cast(V("n"), R()), Cast(V("d"), R())), D(1))), App(Q("Real", "Gamma") ,Add(Div(Mul(Cast(Add(D(1), Mul(V("d"), V("L"))), R()), Cast(V("n"), R())), Cast(V("d"), R())), D(1)))), Div(Pow(Cast(V("d"), R()), Mul(V("L"), V("n"))), Cast(Call("progression" ,V("d"), V("L"), V("n")), R()))))))),
                "For every positive natural d, the Gamma recurrence reduces this ratio to a power of d divided by the progression product.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("ordinary_dvd", All("m", N(), Dvd(Mul(Mul(App(Q("Nat", "factorial") ,Mul(D(1,5), V("m"))), App(Q("Nat", "factorial") ,Mul(D(1,0), V("m")))), App(Q("Nat", "factorial") ,Mul(D(6), V("m")))), Mul(App(Q("Nat", "factorial") ,Mul(D(3,0), V("m"))), App(Q("Nat", "factorial") ,V("m"))))),
                "The product (15m)!(10m)!(6m)! divides (30m)!m!.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", ClaimBody(),
                "Every natural index gives the real cast of an integer. Gamma recurrence and prime valuations prove the assertion for third indices, including zero.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("bala-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => args.Length == 0 ? f : new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Cast(Formula body, Formula type) => Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula NotEq(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Dvd(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Impl(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula RangeProd(Formula size, Formula body) => Seq(new Formula.Subscript(Prod, Seq(V("k"), Sp, InMacro, Sp, App(Q("Finset", "range"), size))), Sp, Parenthesized(body));

    private static Formula ClaimBody() => All("n", N(), Ex("z", new Formula.Integers(), Eq(Call("a", V("n")), Cast(V("z"), R()))));
}

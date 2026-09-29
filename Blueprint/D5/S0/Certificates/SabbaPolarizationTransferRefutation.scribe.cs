using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class SabbaPolarizationTransferRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/SabbaPolarizationTransferRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/sabba2023a362534");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At n = 19 the adiabatic polarization-transfer bound g(19) = 215955/131072 has numerator 215955, while the ratio f(19)/g(19) = 92378/43191 has denominator 43191, so the conjecture of OEIS A362534 fails.",
        H("The conjecture of OEIS A362534 is false at n = 19"),
        Blocks(
            Node("f", "The symmetry-constrained bound", FFormula(),
                "For even n the bound is 2^(1-n) n binomial(n-1, n/2), for odd n it is 2^(1-n) n binomial(n-1, (n-1)/2), as rational numbers; NatDiv and NatMod are the natural quotient and remainder.",
                "f", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("g", "The adiabatic bound", GFormula(),
                "For even n the bound is 2 (1 - 2^(-n) binomial(n, n/2)), for odd n it is 2 (1 - 2^(-n) binomial(n, (n-1)/2)).",
                "g", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture of OEIS A362534", ClaimDefinitionFormula(),
                "For every n at least one, the numerator of g(n) equals the denominator of f(n)/g(n), both in lowest terms (num and den of a rational number).",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A counterexample at n = 19", Disp(new Formula.Not(F.Id("claim"))),
                "Since 19 is odd, f(19) = 2^(-18) 19 binomial(18, 9) = 230945/65536 and g(19) = 2 (1 - 2^(-19) binomial(19, 9)) = 215955/131072. Their ratio is 92378/43191 in lowest terms, whose denominator 43191 differs from the numerator 215955 = 5 times 43191 of g(19).",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sabba-2023-a362534-polarization-transfer-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("sabba-a362534-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Choose(Formula n, Formula k) => Call("choose", n, k);
    private static Formula Half(Formula n) => Call("NatDiv", n, D(2));
    private static Formula IsEven(Formula n) => Equal(Call("NatMod", n, D(2)), D(0));

    private static Formula FFormula()
    {
        Formula n = F.Id("n");
        Formula scale = Mul(new Formula.Power(D(2), Subtract(D(1), n)), n);
        Formula even = Mul(scale, Choose(Subtract(n, D(1)), Half(n)));
        Formula odd = Mul(scale, Choose(Subtract(n, D(1)), Half(Subtract(n, D(1)))));
        return Disp(All("n", Naturals(), Equal(Call("f", n), Call("ite", IsEven(n), even, odd))));
    }

    private static Formula GFormula()
    {
        Formula n = F.Id("n");
        Formula inverse = new Formula.Power(D(2), new Formula.Negate(n));
        Formula even = Mul(D(2), Parenthesized(Subtract(D(1), Mul(inverse, Choose(n, Half(n))))));
        Formula odd = Mul(D(2), Parenthesized(Subtract(D(1), Mul(inverse, Choose(n, Half(Subtract(n, D(1))))))));
        return Disp(All("n", Naturals(), Equal(Call("g", n), Call("ite", IsEven(n), even, odd))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        return All("n", Naturals(), Implies(AtMost(D(1), n),
            Equal(Call("num", Call("g", n)), Call("den", new Formula.Fraction(Call("f", n), Call("g", n))))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}

using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class PrimeSupportBernoulliIndependenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ZetaObservation/PrimeSupportBernoulliIndependence."
            + "prime_support_bits_independent_bernoulli";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime support bits have their power-law Bernoulli marginals inside one "
            + "mutually independent family.",
        H("Prime Support Bernoulli Independence"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-support-bernoulli-independence"),
            DeclarationHandle.Create(Declaration),
            H("Prime support bits are independent Bernoulli variables"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Under the zeta distribution with exponent above one, the support bit "
                        + "at a prime records whether that prime has positive exponent. Its "
                        + "law is Bernoulli with parameter p to the power minus s.")),
                Paragraph(Text(
                    "The family statement uses the full prime-indexed independence predicate. "
                        + "It is obtained by mapping the already independent exponent "
                        + "coordinates through the positive-support predicate, so it controls "
                        + "every finite joint cylinder rather than only separate marginals."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Parenthesize(Formula formula) =>
        F.Seq(F.Open, formula, F.Close);

    private static Formula TheoremFormula()
    {
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula primes = Call("Primes");
        Formula exponent = F.Id("s");
        Formula prime = F.Id("p");
        Formula supportBit = Call("SupportBit", prime);
        Formula zetaLaw = Call("ZetaLaw", exponent);
        Formula parameter = new Formula.Power(
            prime,
            F.Grp(F.Seq(F.Minus, exponent)));
        Formula marginalLaw = new Formula.Relation(
            Call("LawUnder", zetaLaw, supportBit),
            FormulaRelationOperator.Equal,
            Call("Bernoulli", parameter));
        Formula allMarginals = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", primes)],
            marginalLaw);
        Formula jointIndependence = Call(
            "MutuallyIndependentUnder",
            zetaLaw,
            Call("PrimeIndexedFamily", Call("SupportBit")));
        Formula conclusion = new Formula.Logic(
            Parenthesize(allMarginals),
            FormulaLogicOperator.And,
            jointIndependence);
        Formula domain = new Formula.Relation(
            F.D(1), FormulaRelationOperator.LessThan, exponent);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", real)],
            new Formula.Logic(
                domain,
                FormulaLogicOperator.Implies,
                conclusion)));
    }
}

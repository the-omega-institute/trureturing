using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class PrimePrecisionMarginalGainDocument
    : IScribeDocumentDefinition
{
    private const string LeanPath =
        "D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each prime-exponent precision layer reveals a geometrically decreasing binary bit.",
        H("Prime Precision Marginal Gain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-truncated-readout"),
                DeclarationHandle.Create(LeanPath + "primeTruncatedReadout"),
                H("Truncated prime readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The depth-k readout sends an exponent value to its minimum with k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-truncated-readout-law"),
                DeclarationHandle.Create(LeanPath + "primeTruncatedReadoutLaw"),
                H("Law of the truncated readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the pushforward of the canonical prime-exponent PMF by the "
                        + "truncated readout."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-truncated-readout-entropy"),
                DeclarationHandle.Create(LeanPath + "primeTruncatedReadoutEntropy"),
                H("Entropy of the truncated readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The readout entropy is the countable Shannon entropy of its pushforward "
                        + "law, measured in nats."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-precision-marginal-gain"),
                DeclarationHandle.Create(LeanPath + "prime_precision_marginal_gain"),
                H("One precision layer has geometric binary-entropy gain"),
                StatementSource.FromAuthor(MarginalGainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a zeta parameter above one and a prime. The ratio q is the "
                            + "existing primeEvidence value p raised to minus s.")),
                    Paragraph(Text(
                        "The truncated PMF has the original geometric masses below k and one "
                            + "merged tail mass q^k at k. Splitting that tail at the next depth "
                            + "adds q^k times the binary entropy of q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-prime-precision-gain"),
                DeclarationHandle.Create(LeanPath + "first_prime_precision_gain"),
                H("The first precision layer gains full binary entropy"),
                StatementSource.FromAuthor(FirstGainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At k equal to zero, the geometric prefactor is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-entropy-boundary-limits"),
                DeclarationHandle.Create(LeanPath + "binary_entropy_boundary_limits"),
                H("Binary entropy vanishes at both boundary limits"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Continuity and the totalized endpoint values give zero at q approaching "
                        + "zero and at q approaching one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-entropy-half-maximum"),
                DeclarationHandle.Create(LeanPath + "binary_entropy_half_maximum"),
                H("Binary entropy is maximal at one half"),
                StatementSource.FromAuthor(HalfMaximumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At q equal to one half the entropy is log two, its global maximum."))),
                DescribeRole.Theorem))));

    private static Formula MarginalGainFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula primes = Seq(Operatorname, Grp(F.Id("Primes")));
        Formula q = Call("primeEvidence", s, p);
        Formula successor = Add(k, D(1));
        Formula gain = Subtract(Entropy(s, p, successor), Entropy(s, p, k));
        Formula ratioPower = new Formula.Power(Seq(Open, q, Close), Seq(k));
        Formula right = Multiply(ratioPower, Call("binEntropy", q));
        Formula bound = new Formula.Relation(D(1), FormulaRelationOperator.LessThan, s);
        Formula statement = new Formula.Relation(
            gain,
            FormulaRelationOperator.Equal,
            right);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("s"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), primes),
                new Formula.BoundVariable(FormulaIdentifier.Create("k"), naturals),
            ],
            new Formula.Logic(bound, FormulaLogicOperator.Implies, statement)));
    }

    private static Formula FirstGainFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula q = Call("primeEvidence", s, p);
        Formula gain = Subtract(Entropy(s, p, D(1)), Entropy(s, p, D(0)));
        return Disp(new Formula.Relation(
            gain,
            FormulaRelationOperator.Equal,
            Call("binEntropy", q)));
    }

    private static Formula BoundaryFormula()
    {
        Formula entropy = F.Id("binEntropy");
        Formula zero = D(0);
        Formula one = D(1);
        Formula atZero = Tendsto(entropy, Nhds(zero), Nhds(zero));
        Formula atOne = Tendsto(entropy, Nhds(one), Nhds(zero));
        return Disp(new Formula.Logic(atZero, FormulaLogicOperator.And, atOne));
    }

    private static Formula HalfMaximumFormula()
    {
        Formula q = F.Id("q");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula logTwo = new Formula.Apply(Log, [D(2)]);
        Formula value = new Formula.Relation(
            Call("binEntropy", half),
            FormulaRelationOperator.Equal,
            logTwo);
        Formula upperBound = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("q"), reals)],
            new Formula.Relation(
                Call("binEntropy", q),
                FormulaRelationOperator.LessThanOrEqual,
                logTwo));
        return Disp(new Formula.Logic(value, FormulaLogicOperator.And, upperBound));
    }

    private static Formula Entropy(Formula s, Formula p, Formula depth) =>
        Call("primeTruncatedReadoutEntropy", s, p, depth);

    private static Formula Tendsto(Formula function, Formula source, Formula target) =>
        new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("Tendsto"))),
            [function, source, target]);

    private static Formula Nhds(Formula point) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("nhds"))), [point]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}

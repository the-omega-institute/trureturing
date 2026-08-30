using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ObserverScaleDivisorNonidentifiabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Adelic/ObserverScaleDivisorNonidentifiability."
            + "observer_scale_not_recoverable_from_spectral_divisor";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct positive observer parameters and distinct scale ratios can produce "
            + "spectral zeta functions with the same zero-pole divisor.",
        H("Observer Scale Divisor Nonidentifiability"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-scale-divisor-nonidentifiability"),
            DeclarationHandle.Create(Declaration),
            H("The spectral divisor does not determine observer scale"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each observer reading is constructed from its positive circumference P, "
                        + "positive propagation coefficient c, and the Riemann zeta function.")),
                Paragraph(Text(
                    "The two witnesses have different P, different c, and different P over c. "
                        + "At every complex point, both readings have the same meromorphic order "
                        + "as the Riemann zeta function.")),
                Paragraph(Text(
                    "The proof applies the analytic nonzero-factor order theorem to the explicit "
                        + "exponential scale factor, so equality records zeros and poles with "
                        + "multiplicity rather than only equality of zero sets."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula positiveReal = Call("Ioi", D(0), real);
        Formula p1 = F.Id("P1");
        Formula c1 = F.Id("c1");
        Formula p2 = F.Id("P2");
        Formula c2 = F.Id("c2");
        Formula s = F.Id("s");
        Formula zetaOrder = Call("meromorphicOrderAt", F.Id("riemannZeta"), s);
        Formula firstOrder = Call(
            "meromorphicOrderAt",
            Call("observerSpectralZeta", p1, c1),
            s);
        Formula secondOrder = Call(
            "meromorphicOrderAt",
            Call("observerSpectralZeta", p2, c2),
            s);
        Formula commonDivisor = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            And(EqualTo(firstOrder, zetaOrder), EqualTo(secondOrder, zetaOrder)));
        Formula conclusions = And(
            NotEqualTo(p1, p2),
            And(
                NotEqualTo(c1, c2),
                And(
                    NotEqualTo(new Formula.Fraction(p1, c1), new Formula.Fraction(p2, c2)),
                    commonDivisor)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("P1", positiveReal),
                Bound("c1", positiveReal),
                Bound("P2", positiveReal),
                Bound("c2", positiveReal),
            ],
            conclusions));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}

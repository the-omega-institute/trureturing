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
        "Every positive observer pair has the same spectral zero-pole divisor, so no "
            + "function of that divisor can recover the observer's scale ratio.",
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
                    "For every two positive observer pairs and every complex point, the two "
                        + "readings have equal meromorphic order. Thus all observers share the "
                        + "same divisor observation, not merely one selected pair.")),
                Paragraph(Text(
                    "The second public conjunct rules out every function from a divisor reading "
                        + "to a real scale ratio that purports to recover P over c for all positive "
                        + "observers. The proof combines universal order equality with two internal "
                        + "positive choices having unequal ratios."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula positiveReal = Call("Ioi", D(0), real);
        Formula p1 = F.Id("P1");
        Formula c1 = F.Id("c1");
        Formula p2 = F.Id("P2");
        Formula c2 = F.Id("c2");
        Formula p = F.Id("P");
        Formula c = F.Id("c");
        Formula s = F.Id("s");
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
            [
                Bound("P1", positiveReal),
                Bound("c1", positiveReal),
                Bound("P2", positiveReal),
                Bound("c2", positiveReal),
                Bound("s", complex),
            ],
            EqualTo(firstOrder, secondOrder));
        Formula observationType = new Formula.TypeArrow(
            complex,
            Call("WithTop", integer));
        Formula recover = F.Id("recover");
        Formula observation = Seq(
            Open,
            s,
            Colon,
            Sp,
            complex,
            Sp,
            Mapsto,
            Sp,
            Call("meromorphicOrderAt", Call("observerSpectralZeta", p, c), s),
            Close);
        Formula recoversEveryRatio = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("P", positiveReal), Bound("c", positiveReal)],
            EqualTo(
                new Formula.Apply(recover, [observation]),
                new Formula.Fraction(p, c)));
        Formula noRecovery = new Formula.Not(new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("recover"),
            new Formula.TypeArrow(observationType, real),
            recoversEveryRatio));

        return Disp(And(commonDivisor, noRecovery));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

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

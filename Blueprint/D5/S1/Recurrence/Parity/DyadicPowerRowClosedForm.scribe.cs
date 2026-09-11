using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class DyadicPowerRowClosedFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/oeis2024a329369");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rows at powers of two are linear plus quadratic, which contradicts a printed sum.",
        H("Dyadic Rows At Powers Of Two"),
        Blocks(
            Paragraph(Text("The row polynomials R(n, x) satisfy R(2n+1, x) = x R(n, x) and, "
                + "for positive n, R(2n, x) = x (R(n, x+1) - R(n, x)), starting from "
                + "R(0, x) = x. Their coefficients form the table T of OEIS A373183, and "
                + "the values at x = 1 form OEIS A329369. Mikhail Kurkov printed on June 5, "
                + "2024 a sum expressing a value at index 2^m n + q through values at the "
                + "indices 2^m (2^(i-1) - 1) + q, quantified over all natural n, m and q. "
                + "The rows at a positive power of two are computed here in closed form, "
                + "and they make the two sides of that sum differ.")),
            Paragraph(Text("Indices are natural numbers and subtraction of indices is "
                + "natural subtraction. Coefficients and values are integers, so the "
                + "subtractions inside them are integer subtractions. The letter v denotes "
                + "the two-adic valuation and w the number of ones in the binary expansion. "
                + "The summation index i runs over an interval of natural numbers.")),
            Node("b", "Values of the rows at one", ValueFormula(),
                "Evaluating a row polynomial at one adds up its coefficients. This is the "
                + "quantity the printed sum relates across indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("kurkovSum", "The printed sum", SumFormula(),
                "The lower limit is one plus the two-adic valuation of n+1 and the upper "
                + "limit is one plus the binary weight of n, which is the length of row n. "
                + "The summand pairs the row coefficient at i with the value at the index "
                + "obtained from i.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("KurkovRowRecurrence", "The printed sum read for every triple",
                RecurrenceFormula(),
                "This is the printed reading, in which q ranges over all natural numbers "
                + "with no relation to m. It is stated as a proposition so that its "
                + "negation can be proved.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b_zero", "The value at zero", Disp(Seq(Call("b", D(0)), Sp, Eq, Sp, D(1))),
                "The row at zero is x, whose value at one is one.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("b_odd_index", "The odd step", OddFormula(),
                "Multiplying a row by x does not change its value at one, so the odd "
                + "step of the printed recurrence holds for these values.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("b_even_index", "The even step", EvenFormula(),
                "The even step is the value at one of the row identity already carried in "
                + "this repository for the same table. So the two printed recurrences that "
                + "define the sequence are consequences here, not assumptions.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("R_two_pow", "Closed form at powers of two", ClosedFormFormula(),
                "Induct on k. The row at index two is x + 2x^2. Passing from the row at "
                + "2^k to the row at 2^(k+1) applies x (P(x+1) - P(x)) to a polynomial "
                + "a x + c x^2, which yields (a + c) x + 2c x^2. Starting from a = 2^k - 1 "
                + "and c = 2^k reproduces the same shape one step up.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("b_two_pow", "Values at powers of two", PowerValueFormula(),
                "Adding the two coefficients of the closed form gives 2^(k+1) - 1. The "
                + "index zero is separate: the row at one is x^2, whose value is one.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("b_two_pow_add_one", "Values just after powers of two", ShiftedValueFormula(),
                "The index 2^k + 1 is odd, so the odd step reduces it to the index "
                + "2^(k-1), whose value is 2^k - 1.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("printed_recurrence_ne_at_two_pow", "The two sides differ at every power of two",
                GapFormula(),
                "Take n = 2^k, m = 0 and q = 1. The lower limit is one because 2^k + 1 is "
                + "odd, and the upper limit is two because the binary weight is one, so the "
                + "sum has the two terms i = 1 and i = 2. The closed form gives the "
                + "coefficients 2^k - 1 and 2^k, and the values at the indices one and two "
                + "are one and three. The sum is therefore 2^(k+2) - 1 while the left side "
                + "is 2^k - 1. Every triple produced here has q at least 2^m, so the family "
                + "says nothing about the reading in which q stays below 2^m.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("not_kurkovRowRecurrence", "The printed reading is false", NegationFormula(),
                "One instance of the previous family, at k = 1, contradicts the printed "
                + "reading. What is settled is that reading alone. The reading in which q "
                + "stays below 2^m is a different assertion and is not settled here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a329369-printed-row-sum-range"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a329369-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ValueFormula() => Disp(Seq(NatBound("n"), Sp,
        Call("b", N()), Sp, Eq, Sp, Call("eval", D(1), Call("R", N()))));

    private static Formula SumFormula() => Disp(Seq(NatBound("n", "m", "q"), Sp,
        Call("S", N(), M(), Q()), Sp, Eq, Sp, SumBody()));

    private static Formula RecurrenceFormula() => Disp(Seq(NatBound("n", "m", "q"), Sp,
        Call("b", Add(Mul(Pow(D(2), M()), N()), Q())), Sp, Eq, Sp, Call("S", N(), M(), Q())));

    private static Formula NegationFormula() => Disp(Seq(Neg, Sp, Open,
        NatBound("n", "m", "q"), Sp,
        Call("b", Add(Mul(Pow(D(2), M()), N()), Q())), Sp, Eq, Sp,
        Call("S", N(), M(), Q()), Close));

    private static Formula SumBody() => Seq(
        new Formula.Subscript(F.Sum, Grp(Seq(Add(D(1), Call("v", Add(N(), D(1)))), Sp, Le, Sp,
            I(), Sp, Le, Sp, Add(Call("w", N()), D(1))))), Sp,
        Call("T", N(), I()), Sp, Cdot, Sp,
        Call("b", Add(Mul(Pow(D(2), M()), Sub(Pow(D(2), Sub(I(), D(1))), D(1))), Q())));

    private static Formula OddFormula() => Disp(Seq(NatBound("r"), Sp,
        Call("b", Add(Mul(D(2), Rr()), D(1))), Sp, Eq, Sp, Call("b", Rr())));

    private static Formula EvenFormula() => Disp(Seq(NatBound("r"), Sp, D(0), Sp, Lt, Sp, Rr(),
        Sp, Implies, Sp, Call("b", Mul(D(2), Rr())), Sp, Eq, Sp,
        Add(Add(Call("b", Rr()), Call("b", Sub(Rr(), Pow(D(2), Call("v", Rr()))))),
            Call("b", Sub(Mul(D(2), Rr()), Pow(D(2), Call("v", Rr())))))));

    private static Formula ClosedFormFormula() => Disp(Seq(NatBound("k"), Sp, D(0), Sp, Lt, Sp,
        K(), Sp, Implies, Sp, Call("R", Pow(D(2), K())), Sp, Eq, Sp,
        Add(Mul(Sub(Pow(D(2), K()), D(1)), X()),
            Mul(Pow(D(2), K()), new Formula.Power(X(), D(2))))));

    private static Formula PowerValueFormula() => Disp(Seq(NatBound("k"), Sp,
        Call("b", Pow(D(2), K())), Sp, Eq, Sp, Sub(Pow(D(2), Add(K(), D(1))), D(1))));

    private static Formula ShiftedValueFormula() => Disp(Seq(NatBound("k"), Sp, D(0), Sp, Lt, Sp,
        K(), Sp, Implies, Sp, Call("b", Add(Pow(D(2), K()), D(1))), Sp, Eq, Sp,
        Sub(Pow(D(2), K()), D(1))));

    private static Formula GapFormula() => Disp(Seq(NatBound("k"), Sp, D(0), Sp, Lt, Sp, K(), Sp,
        Implies, Sp, Call("b", Add(Mul(Pow(D(2), D(0)), Pow(D(2), K())), D(1))), Sp, Neq, Sp,
        Call("S", Pow(D(2), K()), D(0), D(1))));

    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula Q() => F.Id("q");
    private static Formula I() => F.Id("i");
    private static Formula K() => F.Id("k");
    private static Formula Rr() => F.Id("r");
    private static Formula X() => F.Id("x");
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula NatBound(params string[] names)
    {
        Formula[] parts = new Formula[names.Length * 2 - 1];
        for (int index = 0; index < names.Length; index++)
        {
            parts[index * 2] = F.Id(names[index]);
            if (index + 1 < names.Length)
            {
                parts[index * 2 + 1] = Comma;
            }
        }

        return Seq(Forall, Sp, Seq(parts), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma);
    }
}

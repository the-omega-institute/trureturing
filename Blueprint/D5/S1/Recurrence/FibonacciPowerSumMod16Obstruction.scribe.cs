using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciPowerSumMod16ObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci residues modulo sixteen give a finite obstruction to even perfect-power sums.",
        H("Fibonacci Perfect-Power Sum Obstruction Modulo Sixteen"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-power-sum-square-residues-sixteen"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.squareResidues16"),
                H("Square residues modulo sixteen"),
                StatementSource.FromAuthor(SquareResiduesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This finite set is the target of the exhaustive square-residue "
                        + "classification and the complement used in the obstruction set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-power-sum-period-twenty-four"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction."
                        + "fib_mod_sixteen_period"),
                H("Fibonacci period and index reduction modulo sixteen"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two kernel-computed initial congruences and the two-step Fibonacci "
                        + "recurrence establish period twenty-four. Induction on the quotient "
                        + "by twenty-four then reduces every index to its remainder."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-power-sum-square-classification"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.square_mod_sixteen"),
                H("Classification of squares modulo sixteen"),
                StatementSource.FromAuthor(SquareClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reducing the base modulo sixteen leaves sixteen cases, each discharged "
                        + "by kernel evaluation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-power-sum-obstruction-pairs"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.E16"),
                H("Obstructed residue pairs"),
                StatementSource.FromAuthor(E16Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set contains exactly those ordered residues modulo twenty-four "
                        + "whose Fibonacci sum is not a square residue modulo sixteen."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-power-sum-obstruction-cardinality"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.E16_card"),
                H("Cardinality of the obstruction set"),
                StatementSource.FromAuthor(E16CardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Ordinary kernel decision, with only the recursion-depth option raised "
                        + "locally, counts 440 obstructed pairs among the 576 possibilities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-power-sum-even-power-obstruction"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction."
                        + "even_power_sum_obstruction"),
                H("Even perfect powers are excluded on every obstructed residue pair"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An even exponent writes the power as a square. Equality with a "
                            + "Fibonacci sum would therefore put its residue in the square "
                            + "set, while period reduction transfers that residue to the pair "
                            + "already excluded by E16.")),
                    Paragraph(Text(
                        "The second conjunct is the source's independent numerical check: "
                            + "Fibonacci numbers at indices thirty-six and twelve sum to the "
                            + "square of 3864. This modular result does not prove the full "
                            + "Luca-Patel conjecture."))),
                DescribeRole.Theorem))));

    private static Formula SquareResiduesFormula() =>
        Disp(Seq(
            Residues(), Colon, Sp, Call("Finset", Naturals()), Sp, Colon, Eq, Sp,
            new Formula.SetLiteral([D(0), D(1), D(4), D(9)]), Dot));

    private static Formula PeriodFormula()
    {
        Formula n = F.Id("n");
        Formula first = Seq(
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Mod(Fib(Seq(n, Sp, Plus, Sp, D(2, 4))), D(1, 6)), Sp, Eq, Sp,
            Mod(Fib(n), D(1, 6)));
        Formula second = Seq(
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Mod(Fib(n), D(1, 6)), Sp, Eq, Sp,
            Mod(Fib(Mod(n, D(2, 4))), D(1, 6)));

        return Disp(new Formula.Aligned([
            Seq(Left, Open, first, Right, Close, Sp, Land),
            Seq(Left, Open, second, Right, Close, Dot),
        ]));
    }

    private static Formula SquareClassificationFormula()
    {
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, y, Colon, Sp, Naturals(), Comma, Sp,
            Mod(Power(y, D(2)), D(1, 6)), Sp, InMacro, Sp, Residues(), Dot));
    }

    private static Formula E16Formula()
    {
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula pair = Tuple(r, s);
        Formula pairType = Seq(Call("Fin", D(2, 4)), Sp, Times, Sp, Call("Fin", D(2, 4)));
        Formula excluded = Seq(
            Mod(
                Seq(Left, Open, Fib(r), Sp, Plus, Sp, Fib(s), Right, Close),
                D(1, 6)),
            Sp, InMacro, Sp, Residues());
        Formula domainAndCondition = Seq(
            pairType, Comma, Sp, Neg, Sp, Grp(excluded));

        return Disp(Seq(
            E16(), Colon, Sp, Call("Finset", pairType), Sp, Colon, Eq, Sp,
            new Formula.SetBuilder(pair, pair, domainAndCondition), Dot));
    }

    private static Formula E16CardFormula() =>
        Disp(Seq(Call("card", E16()), Sp, Eq, Sp, D(4, 4, 0), Dot));

    private static Formula ObstructionFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula y = F.Id("y");
        Formula a = F.Id("a");
        Formula reducedPair = Tuple(Mod(n, D(2, 4)), Mod(m, D(2, 4)));
        Formula powerExclusion = Seq(
            Forall, Sp, n, Comma, Sp, m, Colon, Sp, Naturals(), Comma, RowBreak,
            reducedPair, Sp, InMacro, Sp, E16(), Sp, Implies, RowBreak,
            Forall, Sp, y, Comma, Sp, a, Colon, Sp, Naturals(), Comma, RowBreak,
            Call("Even", a), Sp, Implies, Sp, D(2), Sp, Le, Sp, a, Sp, Implies, RowBreak,
            Power(y, a), Sp, Neq, Sp, Fib(n), Sp, Plus, Sp, Fib(m));
        Formula numericalCheck = Seq(
            Fib(D(3, 6)), Sp, Plus, Sp, Fib(D(1, 2)), Sp, Eq, Sp,
            Power(D(3, 8, 6, 4), D(2)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Left, Open, powerExclusion, Right, Close, Sp, Land, RowBreak,
            Left, Open, numericalCheck, Right, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Fib(Formula index) => Call("fib", index);

    private static Formula Mod(Formula value, Formula modulus) =>
        new Formula.Modulo(value, modulus);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula Tuple(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula Residues() => Seq(F.Id("R"), Underscore, Grp(D(1, 6)));

    private static Formula E16() => Seq(F.Id("E"), Underscore, Grp(D(1, 6)));
}

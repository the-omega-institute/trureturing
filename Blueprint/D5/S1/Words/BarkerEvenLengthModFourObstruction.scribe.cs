using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class BarkerEvenLengthModFourObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A boundary autocorrelation congruence gives the classical divisibility-by-four "
            + "obstruction for even Barker sequences, together with explicit finite witnesses.",
        H("Even-Length Barker Sequences and the Mod-Four Boundary Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("barker-aperiodic-correlation"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction.aperiodicCorrelation"),
                H("Aperiodic correlation on a finite prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a sequence a and natural numbers n and k, the kth aperiodic "
                        + "correlation is the sum of a(i)a(i+k) over 0 <= i < n-k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("barker-prefix-condition"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction.IsBarker"),
                H("The Barker condition on a finite prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first n entries must all be signs, and every nonzero shift below n "
                        + "must have aperiodic correlation of absolute value at most one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("barker-correlation-boundary-congruences"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction."
                        + "barker_correlation_congruences"),
                H("Parity and mod-four boundary congruences"),
                StatementSource.FromAuthor(CorrelationCongruencesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every sign product is congruent to one modulo two, proving the first "
                        + "conjunct for every shift. For the second conjunct, the pointwise "
                        + "identity xy = x-y+1 modulo four telescopes at stride two and leaves "
                        + "exactly the two boundary correlations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("even-barker-length-mod-four"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction."
                        + "even_barker_length_mod_four"),
                H("Even Barker lengths above two are divisible by four"),
                StatementSource.FromAuthor(ModFourObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At positive even shifts the parity congruence and Barker bound force the "
                        + "correlation to vanish. Applying this at shifts two and n-2 in the "
                        + "mod-four boundary congruence proves divisibility by four. The second "
                        + "conjunct records the resulting exclusion of every length congruent "
                        + "to two modulo four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-even-barker-length-mod-four-two"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction."
                        + "no_even_barker_of_mod_four_eq_two"),
                H("The modulo-four-two exclusion as a named companion"),
                StatementSource.FromAuthor(ModFourExclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exclusion is exposed as an addressable bind-only companion of the "
                        + "divisibility theorem, with exactly the hypotheses named in the "
                        + "preregistered remark."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("barker-length-thirteen-witness"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction.barker13"),
                H("The length-thirteen Barker word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function has positive entries at indices 0, 1, 2, 3, 4, 7, 8, 10, "
                        + "and 12 and negative entries elsewhere, so its first thirteen signs "
                        + "are +++++--++-+-+."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("barker-length-four-witness"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction.barker4"),
                H("The length-four Barker word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function is positive at indices 0, 1, and 2 and negative elsewhere, "
                        + "so its first four signs are +++-."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("equal-odd-correlation-witness"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction.oddEqualEight"),
                H("A length-eight equal-correlation non-Barker word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function is negative only at index 6, so its first eight signs are "
                        + "++++++-+."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("barker-obstruction-finite-witnesses"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BarkerEvenLengthModFourObstruction."
                        + "barker_obstruction_witnesses"),
                H("Finite witnesses for Barker and equal-correlation behavior"),
                StatementSource.FromAuthor(WitnessesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Kernel enumeration verifies all nontrivial correlations for the classical "
                        + "length-thirteen and length-four Barker words. It also computes the "
                        + "first and third correlations of ++++++-+ as three and verifies that "
                        + "this length-eight word is not Barker, without using native_decide."))),
                DescribeRole.Theorem))));

    private static Formula CorrelationCongruencesFormula()
    {
        Formula a = F.Id("a");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula binary = BinaryPrefix(a, n);
        Formula parity = Seq(
            Forall, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            k, Sp, Le, Sp, n, Sp, Implies, Sp,
            Congruent(Correlation(a, n, k), Seq(n, Sp, Minus, Sp, k), D(2)));
        Formula boundary = Seq(
            D(2), Sp, Le, Sp, n, Sp, Implies, Sp,
            Congruent(
                Seq(
                    Correlation(a, n, D(2)), Sp, Plus, Sp,
                    Correlation(a, n, Seq(n, Sp, Minus, Sp, D(2)))),
                n,
                D(4)));

        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, SequenceType(), Comma, Sp,
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Open, binary, Close, Sp, Implies, Sp,
            Open,
            Open, parity, Close, Sp, Land, Sp,
            Open, boundary, Close,
            Close, Dot));
    }

    private static Formula ModFourObstructionFormula()
    {
        Formula a = F.Id("a");
        Formula n = F.Id("n");
        Formula hypotheses = Seq(
            Call("Even", n), Sp, Land, Sp, D(2), Sp, Lt, Sp, n);
        Formula divisibility = Seq(
            Barker(a, n), Sp, Implies, Sp,
            new Formula.Modulo(n, D(4)), Sp, Eq, Sp, D(0));
        Formula exclusion = Seq(
            new Formula.Modulo(n, D(4)), Sp, Eq, Sp, D(2), Sp, Implies, Sp,
            Neg, Sp, Barker(a, n));

        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, SequenceType(), Comma, Sp,
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Open, hypotheses, Close, Sp, Implies, Sp,
            Open,
            Open, divisibility, Close, Sp, Land, Sp,
            Open, exclusion, Close,
            Close, Dot));
    }

    private static Formula WitnessesFormula()
    {
        Formula thirteen = Barker(Seq(F.Id("barker"), Underscore, Grp(D(1, 3))), D(1, 3));
        Formula four = Barker(Seq(F.Id("barker"), Underscore, Grp(D(4))), D(4));
        Formula eight = F.Id("oddEqualEight");
        Formula nonBarkerWitness = Seq(
            Correlation(eight, D(8), D(1)), Sp, Eq, Sp, D(3), Sp, Land, Sp,
            Correlation(eight, D(8), D(3)), Sp, Eq, Sp, D(3), Sp, Land, Sp,
            Neg, Sp, Barker(eight, D(8)));

        return Disp(Seq(
            thirteen, Sp, Land, Sp,
            four, Sp, Land, Sp,
            Open, nonBarkerWitness, Close, Dot));
    }

    private static Formula ModFourExclusionFormula()
    {
        Formula a = F.Id("a");
        Formula n = F.Id("n");
        Formula hypotheses = Seq(
            Call("Even", n), Sp, Land, Sp,
            D(2), Sp, Lt, Sp, n, Sp, Land, Sp,
            new Formula.Modulo(n, D(4)), Sp, Eq, Sp, D(2));

        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, SequenceType(), Comma, Sp,
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Open, hypotheses, Close, Sp, Implies, Sp,
            Neg, Sp, Barker(a, n), Dot));
    }

    private static Formula BinaryPrefix(Formula sequence, Formula length)
    {
        Formula index = F.Id("i");
        Formula value = Apply(sequence, index);
        return Seq(
            Forall, Sp, index, Colon, Sp, Naturals(), Comma, Sp,
            index, Sp, Lt, Sp, length, Sp, Implies, Sp,
            Open,
            value, Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            value, Sp, Eq, Sp, Minus, D(1),
            Close);
    }

    private static Formula Correlation(Formula sequence, Formula length, Formula shift) =>
        Call("aperiodicCorrelation", sequence, length, shift);

    private static Formula Barker(Formula sequence, Formula length) =>
        Call("IsBarker", sequence, length);

    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(
            left, Sp, Equiv, Sp, right, Sp,
            Open, Operatorname, Grp(F.Id("mod")), Sp, modulus, Close);

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

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula SequenceType() =>
        Seq(Naturals(), Sp, To, Sp, Integers());
}

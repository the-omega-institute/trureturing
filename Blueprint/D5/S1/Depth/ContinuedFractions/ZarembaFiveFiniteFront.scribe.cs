using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class ZarembaFiveFiniteFrontDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fuelled Euclidean checker and a kernel-decided witness table certify the "
            + "bound five for every denominator from two through 1024.",
        H("Zaremba Five Finite Front"),
        Blocks(
            Paragraph(Text(
                "The quotient trace records the Euclidean quotient and recurses on the "
                    + "strictly smaller remainder. The Boolean checker separately tests "
                    + "coprimality, numerator range, and the digit bound.")),
            Describe.Lean(
                DescribeId.Create("fuelled-euclidean-quotient-trace"),
                DeclarationHandle.Create(Prefix + "cfDigitsAux"),
                H("Fuelled Euclidean quotient trace"),
                StatementSource.FromAuthor(CfDigitsAuxFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero-fuel trace is empty. At positive fuel, a zero divisor again gives "
                        + "the empty trace; otherwise the next digit is the natural-number "
                        + "quotient and recursion continues with the divisor and remainder."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("continued-fraction-digits"),
                DeclarationHandle.Create(Prefix + "cfDigits"),
                H("Continued-fraction digits"),
                StatementSource.FromAuthor(CfDigitsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public quotient trace starts the fuelled recursion with q plus one "
                        + "steps."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zaremba-witness"),
                DeclarationHandle.Create(Prefix + "ZarembaWitness"),
                H("Zaremba witness"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A witness is coprime to the denominator, lies strictly between zero and the "
                        + "denominator, and has every continued-fraction digit at most A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zaremba-boolean-checker"),
                DeclarationHandle.Create(Prefix + "zarembaCheck"),
                H("Zaremba Boolean checker"),
                StatementSource.FromAuthor(CheckFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The checker is the Boolean conjunction of the three arithmetic tests and "
                        + "the bounded-digits test."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zaremba-five-witness-table"),
                DeclarationHandle.Create(Prefix + "zarembaFiveWitnessTable"),
                H("Explicit Zaremba-five witness table"),
                StatementSource.FromAuthor(WitnessTableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the explicit kernel-decided list of numerator witnesses indexed by "
                        + "q from zero through 1024. Its concrete Lean value has length 1025."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zaremba-five-numerator"),
                DeclarationHandle.Create(Prefix + "zarembaFiveNumerator"),
                H("Zaremba-five numerator lookup"),
                StatementSource.FromAuthor(NumeratorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator for q is the q-th table entry, with zero as the out-of-range "
                        + "default."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("euclidean-checker-soundness"),
                DeclarationHandle.Create(Prefix + "cfDigits_checker_sound"),
                H("Euclidean checker soundness"),
                StatementSource.FromAuthor(CheckerSoundnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "These three clauses expose the quotient-remainder recursion, strict "
                        + "remainder descent, and Boolean-to-propositional soundness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zaremba-five-certificate"),
                DeclarationHandle.Create(Prefix + "zarembaFiveCertificate"),
                H("Public finite Zaremba certificate"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This publicly addressable theorem is the named finite escape witness. "
                        + "Lean's kernel evaluates all 1025 rows of the witness table."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zaremba-five-through-1024"),
                DeclarationHandle.Create(Prefix + "zaremba_five_upto_certified"),
                H("Zaremba five through 1024"),
                StatementSource.FromAuthor(FiniteFrontFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The embedded 1025-row table is checked by Lean's kernel decision "
                            + "procedure. Each admissible denominator selects its table row "
                            + "and checker soundness converts that row into a witness.")),
                    Paragraph(Text(
                        "The remaining conjuncts pin the smallest denominator, the minimal "
                            + "numerator at 54, two exact quotient traces, and rejection when "
                            + "the digit six exceeds the bound five."))),
                DescribeRole.Theorem))));

    private static Formula CfDigitsAuxFormula()
    {
        var fuel = F.Id("fuel");
        var a = F.Id("a");
        var q = F.Id("q");
        var naturals = Naturals();
        var listNaturals = Call("List", naturals);
        var positiveStep = Call("if",
            Seq(q, Sp, Eq, Sp, D(0)),
            List(),
            Call("cons",
                new Formula.Floor(new Formula.Fraction(a, q)),
                Call("cfDigitsAux", fuel, q, new Formula.Modulo(a, q))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            F.Id("cfDigitsAux"), Sp, Colon, Sp,
            naturals, Sp, To, Sp, naturals, Sp, To, Sp, naturals,
            Sp, To, Sp, listNaturals, Comma, RowBreak, Grp(),
            Forall, Sp, a, Comma, Sp, q, Sp, InMacro, Sp, naturals, Comma, Esc,
            Call("cfDigitsAux", D(0), a, q), Sp, Eq, Sp, List(), Comma,
            RowBreak, Grp(),
            Forall, Sp, fuel, Comma, Sp, a, Comma, Sp, q,
            Sp, InMacro, Sp, naturals, Comma, Esc,
            Call("cfDigitsAux", Seq(fuel, Sp, Plus, Sp, D(1)), a, q),
            Sp, Eq, Sp, positiveStep, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CfDigitsFormula()
    {
        var a = F.Id("a");
        var q = F.Id("q");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, q, Sp, InMacro, Sp, Naturals(), Comma, Esc,
            CfDigits(a, q), Sp, Eq, Sp,
            Call("cfDigitsAux", Seq(q, Sp, Plus, Sp, D(1)), a, q), Dot));
    }

    private static Formula WitnessFormula()
    {
        var A = F.Id("A");
        var a = F.Id("a");
        var d = F.Id("d");
        var q = F.Id("q");
        var digitBound = Parenthesized(Seq(
            Forall, Sp, d, Sp, InMacro, Sp, CfDigits(a, q), Comma, Esc,
            d, Sp, Leq, Sp, A));
        var witnessBody = Parenthesized(Seq(
            Call("Coprime", a, q), Sp, Land, Sp,
            Parenthesized(Seq(
                D(0), Sp, Lt, Sp, a, Sp, Land, Sp,
                Parenthesized(Seq(a, Sp, Lt, Sp, q, Sp, Land, Sp, digitBound))))));

        return Disp(Seq(
            Forall, Sp, A, Comma, Sp, a, Comma, Sp, q,
            Sp, InMacro, Sp, Naturals(), Comma, Esc,
            Witness(A, a, q), Sp, Iff, Sp, witnessBody, Dot));
    }

    private static Formula CheckFormula()
    {
        var A = F.Id("A");
        var a = F.Id("a");
        var q = F.Id("q");
        var checkerBody = Parenthesized(Seq(
            Call("decide", Call("Coprime", a, q)), Sp, Amp, Amp, Sp,
            Parenthesized(Seq(
                Call("decide", Seq(D(0), Sp, Lt, Sp, a)), Sp, Amp, Amp, Sp,
                Parenthesized(Seq(
                    Call("decide", Seq(a, Sp, Lt, Sp, q)), Sp, Amp, Amp, Sp,
                    Call("digitsBounded", A, CfDigits(a, q))))))));

        return Disp(Seq(
            Forall, Sp, A, Comma, Sp, a, Comma, Sp, q,
            Sp, InMacro, Sp, Naturals(), Comma, Esc,
            Check(A, a, q), Sp, Eq, Sp, checkerBody, Dot));
    }

    private static Formula WitnessTableFormula() => Disp(Seq(
        F.Id("zarembaFiveWitnessTable"), Sp, Colon, Sp,
        Call("List", Naturals()), Dot));

    private static Formula NumeratorFormula()
    {
        var q = F.Id("q");
        return Disp(Seq(
            Forall, Sp, q, Sp, InMacro, Sp, Naturals(), Comma, Esc,
            Call("zarembaFiveNumerator", q), Sp, Eq, Sp,
            Call("getD", F.Id("zarembaFiveWitnessTable"), q, D(0)), Dot));
    }

    private static Formula CheckerSoundnessFormula()
    {
        var A = F.Id("A");
        var a = F.Id("a");
        var d = F.Id("d");
        var q = F.Id("q");
        var naturals = Naturals();

        var step = Parenthesized(Seq(
            Forall, Sp, a, Comma, Sp, q, Sp, InMacro, Sp, naturals, Comma, Esc,
            D(0), Sp, Lt, Sp, q, Sp, Rightarrow, Sp,
            CfDigits(a, q), Sp, Eq, Sp,
            Call("cons", new Formula.Floor(new Formula.Fraction(a, q)),
                Call("cfDigitsAux", q, q, new Formula.Modulo(a, q)))));
        var descent = Parenthesized(Seq(
            Forall, Sp, a, Comma, Sp, q, Sp, InMacro, Sp, naturals, Comma, Esc,
            D(0), Sp, Lt, Sp, q, Sp, Rightarrow, Sp,
            new Formula.Modulo(a, q), Sp, Lt, Sp, q));
        var soundness = Parenthesized(Seq(
            Forall, Sp, A, Comma, Sp, a, Comma, Sp, q,
            Sp, InMacro, Sp, naturals, Comma, Esc,
            Check(A, a, q), Sp, Eq, Sp, F.Id("true"), Sp, Rightarrow, Sp,
            Witness(A, a, q)));

        return Disp(Seq(
            step, Sp, Land, RowBreak, Grp(),
            descent, Sp, Land, RowBreak, Grp(),
            soundness, Dot));
    }

    private static Formula CertificateFormula()
    {
        var q = F.Id("q");
        var guardedCheck = Parenthesized(Seq(
            q, Sp, Mapsto, Sp,
            Call("decide", Seq(q, Sp, Lt, Sp, D(2))), Sp, Lor, Sp,
            Check(D(5), Call("zarembaFiveNumerator", q), q)));

        return Disp(Seq(
            Call("all", Call("range", D(1, 0, 2, 5)), guardedCheck),
            Sp, Eq, Sp, F.Id("true"), Dot));
    }

    private static Formula FiniteFrontFormula()
    {
        var a = F.Id("a");
        var q = F.Id("q");
        var naturals = Naturals();

        var universal = Parenthesized(Seq(
            Forall, Sp, q, Sp, InMacro, Sp, naturals, Comma, Esc,
            D(2), Sp, Leq, Sp, q, Sp, Rightarrow, Sp,
            q, Sp, Leq, Sp, D(1, 0, 2, 4), Sp, Rightarrow, Sp,
            Exists, Sp, a, Sp, InMacro, Sp, naturals, Comma, Esc,
            Witness(D(5), a, q)));
        var minimal = Parenthesized(Seq(
            Witness(D(5), D(1, 7), D(5, 4)), Sp, Land, Sp,
            Forall, Sp, a, Sp, InMacro, Sp, Call("Fin", D(1, 7)), Comma, Esc,
            Neg, Sp, Witness(D(5), Call("val", a), D(5, 4))));
        var positiveTrace = Seq(
            CfDigits(D(1, 7), D(5, 4)), Sp, Eq, Sp,
            List(D(0), D(3), D(5), D(1), D(2)));
        var negativePair = Parenthesized(Seq(
            CfDigits(D(1), D(6)), Sp, Eq, Sp, List(D(0), D(6)), Sp, Land, Sp,
            Check(D(5), D(1), D(6)), Sp, Eq, Sp, F.Id("false")));

        return Disp(Seq(
            universal, Sp, Land, RowBreak, Grp(),
            Witness(D(5), D(1), D(2)), Sp, Land, RowBreak, Grp(),
            minimal, Sp, Land, RowBreak, Grp(),
            positiveTrace, Sp, Land, RowBreak, Grp(),
            negativePair, Dot));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula CfDigits(Formula numerator, Formula denominator) =>
        Call("cfDigits", numerator, denominator);

    private static Formula Check(Formula bound, Formula numerator, Formula denominator) =>
        Call("zarembaCheck", bound, numerator, denominator);

    private static Formula Witness(Formula bound, Formula numerator, Formula denominator) =>
        Call("ZarembaWitness", bound, numerator, denominator);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula List(params Formula[] entries)
    {
        var items = new List<Formula> { OpenBracket };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[index]);
        }

        items.Add(CloseBracket);
        return Seq([.. items]);
    }
}

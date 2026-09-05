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
            + "sharp bound five for every denominator from two through 1024.",
        H("Zaremba Five Finite Front"),
        Blocks(
            Paragraph(Text(
                "The quotient trace records the Euclidean quotient and recurses on the "
                    + "strictly smaller remainder. The Boolean checker separately tests "
                    + "coprimality, numerator range, and the digit bound.")),
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

    private static Formula CheckerSoundnessFormula()
    {
        var A = F.Id("A");
        var a = F.Id("a");
        var d = F.Id("d");
        var q = F.Id("q");
        var naturals = Naturals();

        var step = Seq(
            Open, Forall, Sp, a, Comma, Sp, q, Sp, InMacro, Sp, naturals, Comma, Esc,
            D(0), Sp, Lt, Sp, q, Sp, Rightarrow, Sp,
            CfDigits(a, q), Sp, Eq, Sp,
            Call("cons", new Formula.Fraction(a, q),
                Call("cfDigitsAux", q, q, new Formula.Modulo(a, q))), Close);
        var descent = Seq(
            Open, Forall, Sp, a, Comma, Sp, q, Sp, InMacro, Sp, naturals, Comma, Esc,
            D(0), Sp, Lt, Sp, q, Sp, Rightarrow, Sp,
            new Formula.Modulo(a, q), Sp, Lt, Sp, q, Close);
        var soundness = Seq(
            Open, Forall, Sp, A, Comma, Sp, a, Comma, Sp, q,
            Sp, InMacro, Sp, naturals, Comma, Esc,
            Check(A, a, q), Sp, Eq, Sp, F.Id("true"), Sp, Rightarrow, Sp,
            Witness(A, a, q), Close);

        return Disp(Seq(
            step, Sp, Land, RowBreak, Grp(),
            descent, Sp, Land, RowBreak, Grp(),
            soundness, Dot));
    }

    private static Formula CertificateFormula()
    {
        var q = F.Id("q");
        var guardedCheck = Seq(
            Open, q, Sp, Mapsto, Sp,
            Call("decide", Seq(q, Sp, Lt, Sp, D(2))), Sp, Lor, Sp,
            Check(D(5), Call("zarembaFiveNumerator", q), q), Close);

        return Disp(Seq(
            Call("all", Call("range", D(1, 0, 2, 5)), guardedCheck),
            Sp, Eq, Sp, F.Id("true"), Dot));
    }

    private static Formula FiniteFrontFormula()
    {
        var a = F.Id("a");
        var q = F.Id("q");
        var naturals = Naturals();

        var universal = Seq(
            Open, Forall, Sp, q, Sp, InMacro, Sp, naturals, Comma, Esc,
            D(2), Sp, Leq, Sp, q, Sp, Rightarrow, Sp,
            q, Sp, Leq, Sp, D(1, 0, 2, 4), Sp, Rightarrow, Sp,
            Exists, Sp, a, Sp, InMacro, Sp, naturals, Comma, Esc,
            Witness(D(5), a, q), Close);
        var minimal = Seq(
            Open, Witness(D(5), D(1, 7), D(5, 4)), Sp, Land, Sp,
            Forall, Sp, a, Sp, InMacro, Sp, Call("Fin", D(1, 7)), Comma, Esc,
            Neg, Sp, Witness(D(5), a, D(5, 4)), Close);
        var positiveTrace = Seq(
            CfDigits(D(1, 7), D(5, 4)), Sp, Eq, Sp,
            List(D(0), D(3), D(5), D(1), D(2)));
        var negativePair = Seq(
            Open, CfDigits(D(1), D(6)), Sp, Eq, Sp, List(D(0), D(6)), Sp, Land, Sp,
            Check(D(5), D(1), D(6)), Sp, Eq, Sp, F.Id("false"), Close);

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

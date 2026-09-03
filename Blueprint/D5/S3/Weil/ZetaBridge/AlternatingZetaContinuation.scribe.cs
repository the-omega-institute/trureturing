using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class AlternatingZetaContinuationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The paired alternating zeta series gives the eta continuation away from one, "
            + "which excludes real zeta zeros in the open critical interval and makes "
            + "the ordinates of ZeroData nontrivial zeros nonzero.",
        H("Alternating Zeta Continuation and Real-Axis Nonvanishing"),
        Blocks(
            Theorem(
                "alternating-zeta-continuation-away-from-one",
                "tendsto_alternating_partialSums_eta_of_ne_one",
                "The alternating zeta partial sums converge away from one",
                EtaContinuationFormula(),
                "Adjacent terms form an absolutely summable series on every right "
                    + "half-plane bounded away from zero. Locally uniform convergence "
                    + "makes its sum analytic. On real part greater than one, splitting "
                    + "the zeta series into even and odd terms identifies the sum with "
                    + "(1 - 2^(1-s)) zeta(s); the analytic identity principle and a "
                    + "real-axis limit extend the identity to positive real part away "
                    + "from one."),
            Theorem(
                "stated-eta-atom-fails-at-one",
                "alternating_partialSums_eta_atom_fails_at_one",
                "The unqualified continuation statement fails at one",
                EtaFailureAtOneFormula(),
                "At s=1 the alternating harmonic series has a strictly positive paired "
                    + "sum, whereas Mathlib's point value makes the displayed right-hand "
                    + "side zero because its eta prefactor vanishes."),
            Theorem(
                "riemann-zeta-has-no-real-zero-between-zero-and-one",
                "riemannZeta_ne_zero_of_real_mem_Ioo",
                "Riemann zeta has no real zero in the open critical interval",
                RealNonvanishingFormula(),
                "This is a direct corollary of the frozen "
                    + "riemannZeta_ofReal_sign theorem: below one its real part is "
                    + "strictly negative, so the zeta value cannot vanish."),
            Theorem(
                "zero-data-nontrivial-zeros-have-nonzero-imaginary-part",
                "im_ne_zero",
                "ZeroData nontrivial zeros have nonzero imaginary part",
                ZeroDataNonrealFormula(),
                "A nontrivial zero with zero imaginary part would be a real zeta zero "
                    + "strictly between zero and one, contradicting real-axis "
                    + "nonvanishing. Thus separator theorems need no separate hIm "
                    + "assumption for ZeroData entries. This removes a hypothesis only; "
                    + "it does not assert the existence of any new zeros or prove RH."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

    private static Formula EtaContinuationFormula()
    {
        Formula s = F.Id("s");
        Formula premise = And(
            LessThan(D(0), RealPart(s)),
            NotEqual(s, D(1)));
        return Disp(ForAll(
            [Bound("s", ComplexNumbers())],
            Implies(premise, EtaLimit(s))));
    }

    private static Formula EtaFailureAtOneFormula() =>
        Disp(Seq(Neg, Grp(EtaLimit(D(1)))));

    private static Formula RealNonvanishingFormula()
    {
        Formula x = F.Id("x");
        Formula premise = And(LessThan(D(0), x), LessThan(x, D(1)));
        return Disp(ForAll(
            [Bound("x", RealNumbers())],
            Implies(premise, NotEqual(ZetaAt(x), D(0)))));
    }

    private static Formula ZeroDataNonrealFormula()
    {
        Formula z = F.Id("Z");
        Formula n = F.Id("n");
        Formula zero = Call("zero", z, n);
        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("n", Naturals())],
            Implies(
                Call("IsNontrivialZero", zero),
                NotEqual(ImaginaryPart(zero), D(0)))));
    }

    private static Formula EtaLimit(Formula s)
    {
        Formula n = F.Id("n");
        Formula upper = Seq(F.Id("N"), Minus, D(1));
        Formula sign = Seq(Open, Minus, D(1), Close, Caret, Grp(n));
        Formula shifted = Seq(Open, n, Plus, D(1), Close);
        Formula term = Seq(
            sign, Thin,
            shifted, Caret, Grp(Minus, s));
        Formula partialSum = Seq(
            Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(upper), Sp, term);
        Formula factor = Seq(
            Open, D(1), Minus,
            D(2), Caret, Grp(D(1), Minus, s), Close);
        Formula right = Seq(factor, Thin, ZetaAt(s));
        return Seq(
            Lim, Underscore, Grp(F.Id("N"), To, Infty), Sp,
            partialSum, Sp, Eq, Sp, right);
    }

    private static Formula ZetaAt(Formula value) =>
        Seq(Zeta, Open, value, Close);

    private static Formula RealPart(Formula value) =>
        Seq(Re, Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Call("Im", value);

    private static Formula RealNumbers() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula ComplexNumbers() =>
        Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, clauses[index]);
        }

        return result;
    }

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}

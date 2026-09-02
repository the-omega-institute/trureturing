using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ObserverCriteria;

internal sealed class OneObserverTotalPositivityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/ObserverCriteria/OneObserverTotalPositivityCriterion."
            + "one_observer_total_positivity_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonvanishing observer and the analytic PF-infinity bridges reduce total "
            + "positivity to the shifted-square geometry of the zero set.",
        H("One-Observer Total-Positivity Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("one-observer-total-positivity-criterion"),
            DeclarationHandle.Create(Declaration),
            H("One observer identifies RH, total nonnegativity, and PF infinity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a real observer t at which xi is nonzero. Assume the supplied "
                        + "all-finite-minors predicate is equivalent to the supplied PF-infinity "
                        + "predicate, RH implies PF infinity, and PF infinity places every "
                        + "shifted square (z-t)^2 on the nonnegative real axis.")),
                Paragraph(Text(
                    "Taking real and imaginary parts of the square gives 2(Re z-t)Im z=0. "
                        + "If the first factor vanishes, nonnegativity of the square forces "
                        + "Im z=0; otherwise the product identity does so. The final supplied "
                        + "real-zero criterion therefore returns RH.")),
                Paragraph(Text(
                    "The PF-infinity representation and the minors equivalence are hypotheses "
                        + "because neither the repository nor pinned Mathlib packages those "
                        + "analytic bridges. The theorem proves the exact logical closure once "
                        + "they are available and does not reprove nearby frozen criteria."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula rh = F.Id("RH");
        Formula tn = Call("TN", F.Id("Pt"));
        Formula pf = Call("PFInfinity", F.Id("at"));
        Formula xi = F.Id("Xi");
        Formula t = F.Id("t");
        Formula z = F.Id("z");
        Formula x = F.Id("x");
        Formula observer = Seq(Apply(xi, t), Sp, Neq, Sp, D(0));
        Formula shiftedSquare = Equal(
            Seq(Grp(Seq(z, Sp, Minus, Sp, t)), Caret, D(2)), x);
        Formula squareBridge = Seq(
            pf, Sp, Rightarrow, Sp,
            Forall, Sp, z, Comma, Sp,
            Equal(Apply(xi, z), D(0)), Sp, Rightarrow, Sp,
            Exists, Sp, x, InMacro, Reals(), Comma, Sp,
            D(0), Sp, Leq, Sp, x, Sp, Land, Sp, shiftedSquare);
        Formula realZeroBridge = Seq(
            Open, Forall, Sp, z, Comma, Sp,
            Equal(Apply(xi, z), D(0)), Sp, Rightarrow, Sp,
            Equal(Call("Im", z), D(0)), Close,
            Sp, Rightarrow, Sp, rh);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, xi, Colon, Sp, Complexes(), Sp, To, Sp, Complexes(),
                Comma, Sp, t, InMacro, Reals(), Comma),
            Seq(
                observer, Sp, Land, Sp,
                Open, tn, Sp, Leftrightarrow, Sp, pf, Close, Sp, Land),
            Seq(
                Open, rh, Sp, Rightarrow, Sp, pf, Close, Sp, Land, Sp,
                Open, squareBridge, Close, Sp, Land),
            Seq(
                realZeroBridge, Sp, Rightarrow),
            Seq(
                Open, rh, Sp, Leftrightarrow, Sp, tn, Close, Sp, Land, Sp,
                Open, tn, Sp, Leftrightarrow, Sp, pf, Close, Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [argument]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class PushforwardCompositionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Entropy/Forgetting/PushforwardComposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indicator-weighted fiber sums compose over any additive commutative monoid.",
        H("Pushforward Composition"),
        Blocks(
            Paragraph(Text(
                "The frozen module Entropy/Forgetting/CapacityMonotone defines pushforward f p "
                    + "as fun y => sum x, if f x = y then p x else 0, for "
                    + "[Fintype X], and it is imported here. Only the source type is finite; "
                    + "the target carries no finiteness.")),
            Paragraph(Text(
                "The general lemma is the content. sum_indicator_comp mentions no measure of "
                    + "information, no reals, and no pushforward. It holds over an arbitrary "
                    + "additive commutative monoid, so no order, no subtraction, and no real "
                    + "structure is used. pushforward_comp is its real-number instance at M = R, "
                    + "in three lines.")),
            Paragraph(Text(
                "The four existing private copies and the scouting report for this round all fix "
                    + "the values to the real numbers. The general monoid form was obtained by "
                    + "writing it out and compiling it, not by inspecting the definition's type. "
                    + "The report had concluded that the recommended statement carried no "
                    + "decorative hypotheses, and the codomain was the thing it did not "
                    + "question.")),
            Paragraph(Text(
                "Four modules each carry a private copy of the real-valued statement: "
                    + "Entropy/Forgetting/CompletionEntropyMinimality, "
                    + "Entropy/Observation/CompletionInformationChainDecomposition, "
                    + "Entropy/Observation/MultiTargetInformationChain, and "
                    + "Entropy/Submodularity/RefinementInformationDecomposition. They state the "
                    + "same proposition up to the names of the type variables and the functions, "
                    + "and their proofs follow the same route with small differences in the simp "
                    + "set: the same statement, proved four times.")),
            Paragraph(Text(
                "All four modules are frozen, and so is CapacityMonotone. Being frozen, none of "
                    + "them can import this module, and this change removes none of the four "
                    + "copies.")),
            Paragraph(Text(
                "This module has zero consumers today. It does not promise to prevent a future "
                    + "copy.")),
            Paragraph(Text(
                "The value is API, not mathematical novelty. The general lemma is a double-sum "
                    + "exchange with two indicator collapses. pushforward_comp unfolds the "
                    + "definition and applies the general lemma.")),
            Paragraph(Text(
                "Pinned Mathlib was searched by name and by concept for a composition law of "
                    + "indicator-weighted pushforwards of functions. The search found no matching "
                    + "theorem.")),
            Describe.Lean(
                DescribeId.Create("sum-indicator-comp"),
                DeclarationHandle.Create(DeclarationPrefix + "sum_indicator_comp"),
                H("Indicator-weighted finite sums compose"),
                StatementSource.FromAuthor(SumIndicatorCompFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The types X, Y, Z, and M are arbitrary. Only X and Y are finite, and M is "
                        + "an additive commutative monoid. For arbitrary p, f, g, and target, the "
                        + "outer indicator and the inner fiber indicator collapse to the "
                        + "indicator for the composite fiber. There are no further hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pushforward-comp"),
                DeclarationHandle.Create(DeclarationPrefix + "pushforward_comp"),
                H("Pushforwards compose"),
                StatementSource.FromAuthor(PushforwardCompFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite X and Y, a real-valued function p can be pushed first through f "
                        + "and then through g, or directly through their composite. There are no "
                        + "hypotheses on p, and Z has no Fintype instance."))),
                DescribeRole.Theorem))));

    private static Formula SumIndicatorCompFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula zType = F.Id("Z");
        Formula monoid = F.Id("M");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula p = F.Id("p");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula target = F.Id("target");
        Formula zero = Num(0);
        Formula innerFiber = Conditional(
            Seq(Apply(f, x), Sp, Eq, Sp, y),
            Apply(p, x),
            zero);
        Formula outerFiber = Conditional(
            Seq(Apply(g, y), Sp, Eq, Sp, target),
            FiniteSum(x, Parenthesized(innerFiber)),
            zero);
        Formula compositeFiber = Conditional(
            Seq(Apply(g, Apply(f, x)), Sp, Eq, Sp, target),
            Apply(p, x),
            zero);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, xType, Comma, Sp, yType, Comma, Sp,
                zType, Comma, Sp, monoid, Colon, Sp, F.Id("Type"), Comma),
            Seq(
                Typeclass(Apply(F.Id("Fintype"), xType)), Comma, Sp,
                Typeclass(Apply(F.Id("Fintype"), yType)), Comma, Sp,
                Typeclass(Apply(F.Id("AddCommMonoid"), monoid)), Comma),
            Seq(
                Forall, Sp, p, Colon, Sp, Arrow(xType, monoid), Comma, Sp,
                f, Colon, Sp, Arrow(xType, yType), Comma),
            Seq(
                Forall, Sp, g, Colon, Sp, Arrow(yType, zType), Comma, Sp,
                target, Colon, Sp, zType, Comma),
            Seq(
                FiniteSum(y, Parenthesized(outerFiber)), Sp, Eq, Sp,
                FiniteSum(x, Parenthesized(compositeFiber)), Dot),
        ]));
    }

    private static Formula PushforwardCompFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula zType = F.Id("Z");
        Formula p = F.Id("p");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula pushforward = F.Id("pushforward");
        Formula left = Apply(pushforward, g, Apply(pushforward, f, p));
        Formula composite = Grp(g, Sp, Circ, Sp, f);
        Formula right = Apply(pushforward, composite, p);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, xType, Comma, Sp, yType, Comma, Sp,
                zType, Colon, Sp, F.Id("Type"), Comma),
            Seq(
                Typeclass(Apply(F.Id("Fintype"), xType)), Comma, Sp,
                Typeclass(Apply(F.Id("Fintype"), yType)), Comma),
            Seq(
                Forall, Sp, p, Colon, Sp, Arrow(xType, real), Comma, Sp,
                f, Colon, Sp, Arrow(xType, yType), Comma),
            Seq(
                Forall, Sp, g, Colon, Sp, Arrow(yType, zType), Comma),
            Seq(left, Sp, Eq, Sp, right, Dot),
        ]));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typeclass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula FiniteSum(Formula index, Formula summand) =>
        Seq(Sum, Underscore, Grp(index), Sp, summand);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Conditional(
        Formula condition,
        Formula whenTrue,
        Formula whenFalse) =>
        Seq(
            F.Text, Grp(F.Id("if")), Sp, condition, Sp,
            F.Text, Grp(F.Id("then")), Sp, whenTrue, Sp,
            F.Text, Grp(F.Id("else")), Sp, whenFalse);
}

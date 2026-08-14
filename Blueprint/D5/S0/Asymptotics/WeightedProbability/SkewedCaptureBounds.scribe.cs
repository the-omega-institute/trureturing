using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class SkewedCaptureBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var aPrime = Seq(F.Id("a"), Apos);
        var phiA = Seq(Varphi, Underscore, Grp(F.Id("a")));
        var cB = Seq(F.Id("c"), Underscore, Grp(F.Id("b")));
        var fixedSquareA = Call("fixedSquareMass", F.Id("q"), F.Id("f"), F.Id("a"));
        var fixedSquareAPrime = Call("fixedSquareMass", F.Id("q"), F.Id("f"), aPrime);
        var collisionSquareB = Call("collisionSquareMass", F.Id("q"), F.Id("f"), F.Id("b"));
        var singleA = Call("P", Seq(F.Id("E"), Underscore, Grp(F.Id("a"))));
        var singleAPrime = Call("P", Seq(F.Id("E"), Underscore, Grp(aPrime)));
        var pair = Call("Ppair", F.Id("a"), aPrime);
        var escape = Call("Pescape", F.Id("q"), F.Id("f"));
        var uniformQ = Seq(F.Id("q"), Caret, Grp(Mathrm, Grp(F.Id("unif"))));
        var uniformSingleA = Call("P", uniformQ,
            Seq(F.Id("E"), Underscore, Grp(F.Id("a"))));
        var uniformSingleAPrime = Call("P", uniformQ,
            Seq(F.Id("E"), Underscore, Grp(aPrime)));
        var uniformPair = Call("Ppair", uniformQ, F.Id("a"), aPrime);
        var oneQ = Seq(F.Id("q"), Caret, Grp(D(1)));
        var oneQB = Seq(oneQ, Underscore, Grp(F.Id("b")));
        var oneEscape = Call("Pescape", oneQ, F.Id("f"));
        var oneFixedMass = Call("fixedMass", oneQ, F.Id("f"), D(0));
        var singleSum = Seq(Sum, Underscore, Grp(F.Id("a")), Sp, singleA);
        var pairSum = Seq(Sum, Underscore, Grp(F.Id("a"), Lt, aPrime), Sp, pair);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Independent finite listings with column marginals q_b obey the exact skewed capture formulas, two-sided Bonferroni escape bounds, the uniform kernel, and the one-address edge.",
            H("Skewed Capture and Escape Bounds"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("skewed-capture-laws-and-two-sided-escape-bounds"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/SkewedCaptureBounds."
                        + "skewed_capture_bounds"),
                    H("Skewed exact capture laws and escape bounds"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open,
                        Forall, Sp, F.Id("b"), Comma, Sp, F.Id("y"), Comma, Esc,
                        D(0), Leq, Sp, Seq(F.Id("q"), Underscore, Grp(F.Id("b"))),
                        Open, F.Id("y"), Close,
                        Sp, Land, Sp,
                        Forall, Sp, F.Id("b"), Comma, Esc,
                        Sum, Underscore, Grp(F.Id("y")), Sp,
                        Seq(F.Id("q"), Underscore, Grp(F.Id("b"))), Open, F.Id("y"), Close,
                        Sp, Eq, Sp, D(1), Close,
                        Sp, Rightarrow, Sp,
                        Open,
                        Forall, Sp, F.Id("a"), Comma, Esc,
                        singleA, Sp, Eq, Sp, phiA, Sp,
                        Prod, Underscore, Grp(F.Id("b"), Neq, Sp, F.Id("a")), Sp, cB,
                        Sp, Land, Sp,
                        Forall, Sp, F.Id("a"), Comma, Sp, aPrime, Comma, Esc,
                        F.Id("a"), Neq, Sp, aPrime, Sp, Rightarrow, Sp,
                        pair, Sp, Eq, Sp,
                        fixedSquareA, Sp,
                        fixedSquareAPrime, Sp,
                        Prod, Underscore,
                        Grp(F.Id("b"), Neq, Sp, F.Id("a"), Comma, Sp,
                            F.Id("b"), Neq, Sp, aPrime), Sp,
                        collisionSquareB,
                        Sp, Land, Sp,
                        D(1), Minus, singleSum, Sp, Leq, Sp, escape,
                        Sp, Leq, Sp, D(1), Minus, singleSum, Plus, pairSum,
                        Sp, Land, Sp,
                        Open,
                        Forall, Sp, F.Id("a"), Comma, Esc,
                        uniformSingleA, Sp, Eq, Sp, F.Id("k"), Thin, F.Id("n"),
                        Caret, Grp(Minus, F.Id("A")),
                        Sp, Land, Sp,
                        Forall, Sp, F.Id("a"), Comma, Sp, aPrime, Comma, Esc,
                        F.Id("a"), Neq, Sp, aPrime, Sp, Rightarrow, Sp,
                        uniformPair, Sp, Eq, Sp,
                        uniformSingleA, Thin, uniformSingleAPrime, Close,
                        Sp, Land, Sp,
                        Forall, Sp, oneQ, Colon, Sp,
                        Operatorname, Grp(F.Id("Fin")), Open, D(1), Close,
                        Sp, To, Sp, F.Id("Y"), Sp, To, Sp,
                        Mathbb, Grp(F.Id("R")), Comma, Esc,
                        Open,
                        Forall, Sp, F.Id("b"), Comma, Sp, F.Id("y"), Comma, Esc,
                        D(0), Leq, Sp, oneQB, Open, F.Id("y"), Close,
                        Sp, Land, Sp,
                        Forall, Sp, F.Id("b"), Comma, Esc,
                        Sum, Underscore, Grp(F.Id("y")), Sp,
                        oneQB, Open, F.Id("y"), Close,
                        Sp, Eq, Sp, D(1), Close,
                        Sp, Rightarrow, Sp,
                        oneEscape, Sp, Eq, Sp, D(1), Minus, oneFixedMass,
                        Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The address type is finite and linearly ordered only to write each "
                            + "unordered pair once as a<a'. Every matrix cell in column b is an "
                            + "independent draw with nonnegative normalized mass q_b.")),
                        Paragraph(Text(
                            "Here phi_a is fixedMass q f a, c_b is collisionMass q f b, and their "
                            + "superscript-two forms are fixedSquareMass and collisionSquareMass. "
                            + "The finite-product dependency proves the two exact event formulas.")),
                        Paragraph(Text(
                            "Pointwise first- and second-order Bonferroni inequalities are multiplied "
                            + "by the nonnegative listing weights and summed. For uniform marginals, "
                            + "q^unif is the constant marginal (b,y) |-> 1/n, k is card(Fix f), "
                            + "n is card(Y), and A is card(Address). The final clause quantifies "
                            + "separately over every nonnegative normalized Fin(1) marginal q^1; its "
                            + "fixedMass at address zero is the source's phi_0.")),
                        Paragraph(Text(
                            "Thus the effective equivalent-mutant quantity is the weighted fixed-point "
                            + "mass q(Fix f), not the alphabet cardinality. No bijectivity assumption "
                            + "is placed on f."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni")),
            ]));
    }
}

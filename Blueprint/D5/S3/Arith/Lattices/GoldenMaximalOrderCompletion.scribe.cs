using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class GoldenMaximalOrderCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Hodge lattice completes to a stable full-rank lattice, while the "
            + "sqrt-five order has index two in the golden integers.",
        H("Golden Maximal-Order Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-maximal-order-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion."
                        + "golden_maximal_order_completion"),
                H("The golden completion is stable and the order defect is repaired at two"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All ten displayed clauses are the ten conjuncts of the Lean theorem. "
                            + "The ambient GoldenSpace is the rational scalar extension of the "
                            + "ordered six-coordinate Lambda-squared A4 lattice from "
                            + "ExactDualLatticeFormula. The operator goldenOperatorInt is the "
                            + "integer-linear restriction of Phi=(I+J)/2 for that module's "
                            + "explicit Hodge matrix J.")),
                    Paragraph(Text(
                        "The first five clauses state the lattice formula, full rank, containment, "
                            + "stability under every concrete GoldenInt element a+b*phi, and the "
                            + "corresponding leastness property. The leastness quantifier ranges "
                            + "over integral submodules of this same concrete GoldenSpace.")),
                    Paragraph(Text(
                        "The next two clauses use sqrtFiveOrder, the GoldenInt elements whose phi "
                            + "coordinate is even. They state both strict inclusion in GoldenInt "
                            + "and relative additive index two. Thus the Scribe formula records the "
                            + "index of Z[sqrt(5)] in Z[phi], rather than substituting the separate "
                            + "index-two calculation for the completed Hodge lattice.")),
                    Paragraph(Text(
                        "The final three clauses identify the number-field discriminant of the "
                            + "named golden field Q(sqrt(5)) as five, give exact order five for the "
                            + "explicit exterior-square five-cycle on the completed lattice, and "
                            + "state that multiplication by two sends every point of the completed "
                            + "maximal-order lattice into the completed integer lattice. Both "
                            + "lattice completions are closures in the six-coordinate Hodge space "
                            + "over the named finite-place completion above two. No "
                            + "hypothesis, uniqueness claim, or stronger ring-of-integers "
                            + "identification is added here."))),
                DescribeRole.Theorem))));

    private static Formula CompletionFormula()
    {
        Formula wz = F.Id("integerLattice");
        Formula wmax = F.Id("maximalOrderLattice");
        Formula phi = F.Id("goldenOperatorInt");
        Formula sqrtOrder = F.Id("sqrtFiveOrder");
        Formula goldenInt = F.Id("GoldenInt");
        Formula goldenField = F.Id("GoldenNumberField");
        Formula integerCompletion = F.Id("integerLatticeTwoAdicCompletion");
        Formula maximalCompletion = F.Id("maximalOrderLatticeTwoAdicCompletion");
        Formula candidate = F.Id("M");

        Formula stableWmax = Call("IsGoldenStable", wmax);
        Formula stableCandidate = Call("IsGoldenStable", candidate);
        Formula mapped = Call("map", wz, phi);

        return Disp(new Formula.Aligned([
            Seq(wmax, Sp, Eq, Sp, wz, Sp, Plus, Sp, mapped, Sp, Land),
            Seq(Call("IsFullRank", wmax), Sp, Land),
            Seq(wz, Sp, Subseteq, Sp, wmax, Sp, Land),
            Seq(stableWmax, Sp, Land),
            Seq(
                Grp(
                    Forall, Sp, candidate, Comma, Sp,
                    Open, wz, Sp, Subseteq, Sp, candidate, Sp, Land, Sp,
                    stableCandidate, Close, Sp, Rightarrow, Sp,
                    wmax, Sp, Subseteq, Sp, candidate),
                Sp, Land),
            Seq(sqrtOrder, Sp, Subset, Sp, goldenInt, Sp, Land),
            Seq(Call("relIndex", sqrtOrder, goldenInt), Sp, Eq, Sp, D(2), Sp, Land),
            Seq(Call("discr", goldenField), Sp, Eq, Sp, D(5), Sp, Land),
            Seq(Call("orderOf", F.Id("fiveCycleOnCompletion")),
                Sp, Eq, Sp, D(5), Sp, Land),
            Seq(
                Forall, Sp, F.Id("x"), Colon, Sp, maximalCompletion, Comma, Sp,
                D(2), Cdot, Sp, F.Id("x"), Sp, InMacro, Sp, integerCompletion, Dot),
        ]));
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
}

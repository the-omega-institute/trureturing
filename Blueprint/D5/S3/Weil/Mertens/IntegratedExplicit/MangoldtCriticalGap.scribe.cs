using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtCriticalGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The additive gap below the critical Mertens envelope",
        H("The critical coefficient for the complete Mangoldt remainder"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-iff-critical-gap-tendsto-at-top"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap.rh_iff_critical_gap_tendsto_atTop"),
            H("The Riemann hypothesis and divergence of the additive gap"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here U is CompleteMertensPeak.U, the original complete integrated Mangoldt remainder. "
                    + "The coefficient M is firstLiMass. Both the lower bound D and the arguments x range "
                    + "over the reals. The displayed quantifiers unfold convergence to positive infinity.")),
                Paragraph(Text(
                    "With y = log x, RH gives a real normalized zero sum F(y) with cosine terms, "
                    + "nonnegative coefficients, and total coefficient mass M. Write d(y) = M − F(y). "
                    + "The product (1 − cos(γy))(1 + cos(γh)) is nonnegative for each zero ordinate γ. "
                    + "Summing this inequality gives 2d(h) − 4d(y) ≤ 2F(y) − F(y+h) − F(y−h).")),
                Paragraph(Text(
                    "At positive arguments the explicit formula identifies F with the full arithmetic "
                    + "kernel K, whose value at zero is M. Its derivative tends to negative infinity "
                    + "from the right. The mean value theorem on [0,h] therefore shows that d(h)/h "
                    + "tends to positive infinity as h decreases to zero.")),
                Paragraph(Text(
                    "The nonnegative Mangoldt ramps give a weighted midpoint inequality for the normalized "
                    + "arithmetic remainder. At h = exp(−y/2) its smooth part and the correction from the "
                    + "explicit formula give an upper bound proportional to h for the second difference of F. "
                    + "The cosine inequality forces d(y)/h to tend to positive infinity. The bounded additive "
                    + "correction from the explicit formula then gives the stated limit in x. "
                    + "The source derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7060395310.")),
                Paragraph(Text(
                    "Conversely, divergence of the gap gives U(x) ≤ M√x on a real tail. "
                    + "Substituting x = exp(y) and multiplying by exp(−y/2) bounds G(y) by M. "
                    + "The explicit-formula correction then supplies a constant upper bound for K on "
                    + "a positive tail. The affine-tail criterion for K, used with slope zero, gives RH."))),
            DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), Real, body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ImpliesClaim(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Claim()
    {
        var x = F.Id("x");
        var remainder = new Formula.FunctionCall(FormulaIdentifier.Create("U"), [x]);
        var gap = Subtract(Multiply(F.Id("firstLiMass"), Seq(Sqrt, Grp(x))), remainder);
        var tail = Bind(FormulaQuantifier.ForAll, "x",
            ImpliesClaim(Le(F.Id("T"), x), Le(F.Id("D"), gap)));
        var limit = Bind(FormulaQuantifier.ForAll, "D",
            Bind(FormulaQuantifier.Exists, "T", tail));
        return Disp(new Formula.Logic(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            FormulaLogicOperator.Iff, limit));
    }
}

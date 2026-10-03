using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ShortIntervals;

internal sealed class ThreeRowSquareRootLockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common short hull and linked real cubic norms lock an odd integer quotient.",
        H("Three-Row Common-Short-Hull Square-Root Lock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-row-square-root-lock"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ShortIntervals/ThreeRowSquareRootLock.three_row_square_root_lock"),
                H("Positive offsets and the next odd quotient"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The scale S and quotient k are integers. The hull endpoints, offsets, "
                        + "positive roots and sign e are real; e denotes epsilon. "
                        + "Every occurrence of S and k in a real "
                        + "equation uses its integer-to-real embedding; N abbreviates S squared. "
                        + "All three offsets belong to the same interval containing zero. "
                        + "Neither positivity of the offsets nor the quotient conclusion is assumed.")),
                    Paragraph(Text(
                        "Two negative offsets have maximum magnitude s and positive companion r, "
                        + "with s+r at most h. Comparing the norm squares puts both linked root "
                        + "combinations strictly between N(S-1) and N(S+1), forcing k=S and "
                        + "contradicting parity. For positive offsets the arithmetic-geometric "
                        + "comparison gives Q-P>NS. The identity "
                        + "(NS+13N/8)^2-(N+S)^3=S^3(16S^2-23S-64)/64 and P<3N/8 "
                        + "give Q+P<N(S+2). Both signs therefore force k=S+1.")),
                    Paragraph(Text(
                        "This uniform conditional implication does not establish the dyadic scale, "
                        + "complete offset kernels, odd quotient or selected sign of an original "
                        + "Grimm configuration. Distinct actual integer offsets, all owners and "
                        + "factors, Hall conditions, saturation, compositeness, exterior cofactors, "
                        + "the unresolved two-unit equality branch and both nonzero-K orientations "
                        + "remain obligations of the whole problem. A repeated-offset real "
                        + "nonvacuity model is not an original arithmetic instance."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scale = F.Id("S"), quotient = F.Id("k"), width = F.Id("h");
        Formula left = F.Id("l"), offsetB = F.Id("b"), offsetC = F.Id("c"), offsetD = F.Id("d");
        Formula rootQ = F.Id("Q"), rootP = F.Id("P"), epsilon = F.Id("e");
        Formula norm = new Formula.Power(scale, D(2));
        Formula right = Add(left, width);
        Formula hypotheses = And(
            Seq(Operatorname, Grp(F.Id("Even")), Open, scale, Close),
            Le(D(8), scale),
            Seq(Operatorname, Grp(F.Id("Odd")), Open, quotient, Close),
            Le(D(0), width), Le(width, Sub(scale, D(2))),
            Le(left, D(0)), Le(D(0), right),
            Le(left, offsetB), Le(offsetB, right),
            Le(left, offsetC), Le(offsetC, right),
            Le(left, offsetD), Le(offsetD, right),
            Le(D(1), new Formula.Absolute(offsetB)),
            Le(D(1), new Formula.Absolute(offsetC)),
            Le(D(1), new Formula.Absolute(offsetD)),
            Lt(D(0), rootQ), Lt(D(0), rootP),
            Eq(new Formula.Power(rootQ, D(2)),
                Mul(Mul(Add(norm, offsetB), Add(norm, offsetC)), Add(norm, offsetD))),
            Eq(new Formula.Power(rootP, D(2)), Mul(Mul(offsetB, offsetC), offsetD)),
            new Formula.Logic(Eq(epsilon, D(1)), FormulaLogicOperator.Or,
                Eq(epsilon, new Formula.Negate(D(1)))),
            Eq(Add(rootQ, Mul(epsilon, rootP)), Mul(norm, quotient)));
        Formula conclusion = And(Lt(D(0), offsetB), Lt(D(0), offsetC), Lt(D(0), offsetD),
            Eq(quotient, Add(scale, D(1))));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("S", "Z"), Bound("k", "Z"), Bound("h", "R"), Bound("l", "R"),
                Bound("b", "R"), Bound("c", "R"), Bound("d", "R"), Bound("Q", "R"),
                Bound("P", "R"), Bound("e", "R")],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, string domain) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id(domain))));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(params Formula[] parts) => parts.Aggregate(
        (left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));
}

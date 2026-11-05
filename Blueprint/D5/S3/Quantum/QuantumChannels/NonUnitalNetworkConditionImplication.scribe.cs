using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class NonUnitalNetworkConditionImplicationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/mukherjeeganguly2025network");

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula T => F.Id("t");
    private static Formula L1 => Seq(Mathrm, Grp(F.Id("l1")));
    private static Formula L3 => Seq(Mathrm, Grp(F.Id("l3")));
    private static Formula A => F.Id("A");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula U => F.Id("u");
    private static Formula Defect => F.Id("D");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, Reals)), Comma, Sp, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, byte exponent) =>
        new Formula.Power(Parenthesized(value), D(exponent));
    private static Formula Abs(Formula value) => new Formula.Absolute(value);

    private static Formula FirstBound =>
        AtMost(Add(Pow(Add(Abs(T), Abs(L3)), 2), Pow(L1, 2)), D(1));
    private static Formula SecondBound =>
        AtMost(Add(Add(Mul(Mul(D(2), Pow(T, 2)), Pow(L1, 2)), Pow(L1, 4)),
            Pow(Add(Abs(T), Abs(L3)), 4)), D(1));
    private static Formula Claim => All(T, All(L1, All(L3,
        Imp(AtMost(Abs(L1), D(1)),
            Imp(AtMost(Add(Abs(L3), Abs(T)), D(1)),
                Imp(AtMost(Add(Pow(L1, 2), Pow(T, 2)), Pow(Subtract(D(1), Abs(L3)), 2)),
                    And(FirstBound, SecondBound)))))));

    private static Formula Definitions => Seq(
        Eqn(A, Pow(L1, 2)), Comma, Sp,
        Eqn(X, Abs(L3)), Comma, Sp,
        Eqn(Y, Abs(T)), Comma, Sp,
        Eqn(U, Add(X, Y)), Comma, Sp,
        Eqn(Defect, Subtract(Subtract(Pow(Subtract(D(1), X), 2), Pow(Y, 2)), A)));
    private static Formula Quadratic => Add(A, Pow(U, 2));
    private static Formula Quartic => Add(Add(Pow(A, 2), Mul(Mul(D(2), Pow(Y, 2)), A)), Pow(U, 4));
    private static Formula FirstIdentity => Eqn(
        Subtract(D(1), Parenthesized(Quadratic)),
        Add(Defect, Mul(Mul(D(2), X), Parenthesized(Subtract(D(1), U)))));
    private static Formula SecondIdentity => Eqn(
        Subtract(Pow(Quadratic, 2), Parenthesized(Quartic)),
        Mul(Mul(Mul(D(2), A), X), Parenthesized(Add(X, Mul(D(2), Y)))));
    private static Formula QuarticBound => Seq(
        Quartic, Leq, Pow(Quadratic, 2), Leq, D(1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three real parameter constraints for the non-unital channel class imply both quadratic and quartic network bounds.",
        H("Non-unital channel constraints imply the network bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The parameter implication"),
                StatementSource.FromAuthor(Disp(Eqn(
                    Seq(Operatorname, Grp(F.Id("claim"))), Parenthesized(Claim)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every real triple t, l1, l3, the three channel constraints imply both network bounds. "
                    + "In Network_Nonlocality.tex, Eq. (nu3), lines 211–215, supplies the hypotheses; "
                    + "Eq. (resnon1), lines 716–719, supplies the conclusions of the parameter implication. "
                    + "Theorem 3, lines 714–721, uses those conclusions as sufficient conditions for "
                    + "network nonlocality breaking. The observation in lines 733–734 asserts this "
                    + "parameter implication and motivates Conjecture 1. "
                    + "The proposition concerns real parameters; it does not itself assert a theorem about quantum channels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Both bounds follow from nonnegative remainders"),
                StatementSource.FromAuthor(Disp(Claim)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Fix real t, l1, l3 satisfying the three hypotheses, and put:")),
                    new DocumentBlock.DisplayFormula(Definitions),
                    Paragraph(Text(
                        "Squares and absolute values give nonnegative A, x and y. The second hypothesis "
                        + "gives u at most one. Since the square of y equals the square of t, "
                        + "the third hypothesis gives nonnegative D. Expanding the first remainder gives:")),
                    new DocumentBlock.DisplayFormula(FirstIdentity),
                    Paragraph(Text(
                        "Both terms on the right are nonnegative, because x is nonnegative and u is at most one. "
                        + "Thus A plus the square of u is at most one. It is also nonnegative, "
                        + "since A and the square of u are nonnegative. Next expand the second remainder:")),
                    new DocumentBlock.DisplayFormula(SecondIdentity),
                    Paragraph(Text(
                        "The product on the right is nonnegative because A, x and y are nonnegative. "
                        + "Squaring the bounds zero and one for A plus the square of u therefore yields:")),
                    new DocumentBlock.DisplayFormula(QuarticBound),
                    Paragraph(Text(
                        "For the first conclusion, substitute A and u in the quadratic bound and commute x and y. "
                        + "For the second, substitute A, u, x and y in the quartic bound, "
                        + "replace the square of the absolute value of t by the square of t, "
                        + "and collect powers and products. These are the two required inequalities. "
                        + "The bound on the absolute value of l1 is unnecessary for these estimates; "
                        + "the second and third hypotheses suffice."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mukherjee-ganguly-2025-non-unital-network-condition-implication"),
                    ResolutionKind.Proved)))));
}

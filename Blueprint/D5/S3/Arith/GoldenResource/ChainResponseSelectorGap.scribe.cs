using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ChainResponseSelectorGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ChainResponseSelectorGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chain responses stay non-scalar at every length while their selector loss vanishes.",
        H("Chain Response Selector Gap"),
        Blocks(
            Paragraph(Text("Eliminating the hidden chain leaves a two by two effective matrix "
                + "that is diagonal with entries k minus b times eta and k. The quantity eta is "
                + "the squared endpoint of the first inverse column divided by the common mass "
                + "coefficient, and the endpoint is the reciprocal of an integer determinant "
                + "obeying a three term recurrence. So the far boundary of the chain is visible "
                + "in the principal part of the response, not merely in a remainder.")),
            Paragraph(Text("The selector objective at price one half is the log determinant "
                + "minus half the trace. Its loss against the scalar matrix with entry two is "
                + "the quantity studied here. All lengths, indices and matrix entries are as in "
                + "the companion module, and the price one half is a chosen specialisation "
                + "rather than a consequence of the surrounding theory; it lies strictly inside "
                + "the window that the integer selector statement requires at k equal to two.")),
            Node("chainResponseLoss", "The loss at the chosen price", LossFormula(),
                "Expanding the objective at the effective matrix against its value at the "
                + "scalar matrix leaves exactly this scalar expression in eta. Both matrices "
                + "share the second diagonal entry, so only the first contributes.",
                DescribeRole.Definition),
            Node("effective_ne_scalar", "No length gives a scalar response", NonScalarFormula(),
                "The endpoint is the reciprocal of a positive integer determinant and the mass "
                + "coefficient is positive, so eta is positive at every length. The two "
                + "diagonal entries of the effective matrix therefore differ, while a scalar "
                + "diagonal matrix has them equal. This holds for every scalar, not only two.",
                DescribeRole.Lemma),
            Node("chain_response_loss_bounds", "Two sided bound on the loss", BoundsFormula(),
                "For y between zero and one half the remainder of the logarithm past its "
                + "linear term is non-negative and at most twice y squared. The lower side "
                + "applies the logarithm bound to one minus y; the upper side applies it to the "
                + "reciprocal and then uses that the reciprocal of one minus y is at most two. "
                + "Substituting half of eta gives the stated pair.",
                DescribeRole.Lemma),
            Node("chain_response_loss_le_geometric", "The loss falls geometrically",
                GeometricFormula(),
                "The mass coefficient is at least one, so eta is at most the squared endpoint, "
                + "which the companion module bounds by the reciprocal of nine to the length. "
                + "Squaring and halving gives the reciprocal of eighty one to the length. This "
                + "estimate is where the integer recurrence enters the conclusion.",
                DescribeRole.Lemma),
            Node("chain_response_selector_gap_refuted", "No uniform gap survives elimination",
                RefutationFormula(),
                "Given a positive bound, choose a length at which the geometric estimate falls "
                + "below it. The effective matrix at that length is still not scalar. So the "
                + "positive gap that the integer statement gives for integer matrices does not "
                + "transfer to the real responses obtained by elimination. The integer "
                + "statement itself is untouched.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("chain-response-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula LossFormula() => Disp(Seq(NatBound("n"), Sp,
        Call("L", N()), Sp, Eq, Sp,
        Sub(Neg2(Call("log", Sub(D(1), Half()))), Half())));

    private static Formula NonScalarFormula() => Disp(Seq(NatBound("n"), Sp,
        Forall, Sp, F.Id("c"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Call("effective", N(), D(2), D(1)), Sp, Neq, Sp,
        Call("diagonal", F.Id("c"), F.Id("c"))));

    private static Formula BoundsFormula() => Disp(Seq(NatBound("n"), Sp,
        D(0), Sp, Le, Sp, Call("L", N()), Sp, Land, Sp, Call("L", N()), Sp, Le, Sp,
        new Formula.Fraction(new Formula.Power(Call("eta", N()), D(2)), D(2))));

    private static Formula GeometricFormula() => Disp(Seq(NatBound("n"), Sp,
        Call("L", N()), Sp, Le, Sp,
        Mul(new Formula.Fraction(D(1), D(2)),
            new Formula.Power(new Formula.Fraction(D(1), D(8,1)), Add(N(), D(1))))));

    private static Formula RefutationFormula() => Disp(Seq(
        Forall, Sp, F.Id("e"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("e"), Sp, Implies, Sp,
        Exists, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Call("effective", N(), D(2), D(1)), Sp, Neq, Sp, Call("diagonal", D(2), D(2)), Sp,
        Land, Sp, D(0), Sp, Le, Sp, Call("L", N()), Sp, Land, Sp,
        Call("L", N()), Sp, Lt, Sp, F.Id("e")));

    private static Formula Half() => new Formula.Fraction(Call("eta", N()), D(2));
    private static Formula Neg2(Formula x) => new Formula.Negate(x);
    private static Formula N() => F.Id("n");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula NatBound(string name) => Seq(Forall, Sp, F.Id(name), Sp,
        InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma);
}

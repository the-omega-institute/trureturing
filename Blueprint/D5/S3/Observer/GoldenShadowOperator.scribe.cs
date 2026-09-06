using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class GoldenShadowOperatorDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenShadowOperator.golden_shadow_operator_theorem";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive operator satisfying the golden shadow identity is the inverse-golden "
            + "scalar on every nonzero active Hilbert space.",
        H("Golden Shadow Operator"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-shadow-operator-theorem"),
            DeclarationHandle.Create(Declaration),
            H("The golden identity collapses the active operator spectrum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let D be a positive continuous endomorphism of a nontrivial complex "
                        + "Hilbert space. If I equals D plus D squared, continuous functional "
                        + "calculus makes every real spectral value satisfy the same quadratic.")),
                Paragraph(Text(
                    "Positivity excludes the negative root. Thus D is the inverse-golden "
                        + "scalar operator; its complement and square are both the "
                        + "inverse-golden-square scalar operator, and its spectrum and norm "
                        + "have the displayed exact values.")),
                Paragraph(Text(
                    "The source's contraction hypothesis is omitted because the exact norm "
                        + "conclusion already implies it. Nontriviality of the active space is "
                        + "stated explicitly: on the zero space the operator identity still "
                        + "holds, but the spectrum is empty and the norm is zero.")),
                Paragraph(Text(
                    "Repository, receipt, digest, generalized-result, and in-flight branch "
                        + "searches found no equivalent theorem. GoldenTwoShadowBound gives "
                        + "the neighboring sharp inequalities, not this equality-case collapse."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula space = F.Id("E");
        Formula op = F.Id("D");
        Formula identity = F.Id("I");
        Formula type = Call("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula phi = new Formula.LatexMacro(FormulaLatexMacro.Phi);
        Formula phiInverse = Seq(phi, Caret, Grp(Minus, D(1)));
        Formula phiInverseSquare = Seq(Grp(phiInverse), Caret, Grp(D(2)));
        Formula endomorphisms = Call("ContinuousLinearMap", complex, space, space);
        Formula scalar = Call("algebraMap", real, endomorphisms, phiInverse);
        Formula squareScalar = Call(
            "algebraMap", real, endomorphisms, phiInverseSquare);
        Formula square = Seq(op, Caret, Grp(D(2)));

        Formula assumptions = Seq(
            D(0), Sp, Leq, Sp, op, Sp, Land, Sp,
            Equal(identity, Add(op, square)));
        Formula conclusions = Seq(
            Equal(op, scalar), Sp, Land, RowBreak, Grp(),
            Equal(Subtract(identity, op), squareScalar), Sp, Land, RowBreak, Grp(),
            Equal(square, squareScalar), Sp, Land, RowBreak, Grp(),
            Equal(Call("spectrum", real, op),
                Seq(OpenBrace, phiInverse, CloseBrace)), Sp, Land, RowBreak, Grp(),
            Equal(new Formula.Norm(op), phiInverse));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(space, type), Comma, RowBreak, Grp(),
            Typeclass("NormedAddCommGroup", space), Sp, Land, Sp,
            Typeclass("InnerProductSpace", complex, space), Sp, Land, Sp,
            Typeclass("CompleteSpace", space), Sp, Land, Sp,
            Typeclass("Nontrivial", space), Comma, RowBreak, Grp(),
            Forall, Sp, Typed(op, endomorphisms), Comma, Sp,
            Open, assumptions, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusions, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Conditioning;

internal sealed class TargetVisibilityConditionCostDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact target visibility carries a canonical target-specific condition cost.",
        H("Target Visibility and Condition Cost"),
        Blocks(Describe.Lean(
            DescribeId.Create("target-visibility-condition-cost"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Conditioning/TargetVisibilityConditionCost."
                    + "target_visibility_condition_cost"),
            H("Visibility determines a unique minimum-norm cost certificate"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The measurement map is defined on arbitrary finite-dimensional "
                        + "inner-product spaces over a real or complex scalar field. A target "
                        + "is exactly visible when its Riesz functional is constant on every "
                        + "measurement fiber.")),
                Paragraph(Text(
                    "The theorem constructs the state Gramian from the measurement and its "
                        + "adjoint. It then exposes the unique Gram preimage orthogonal to the "
                        + "hidden kernel and the induced observation coefficient.")),
                Paragraph(Text(
                    "That coefficient solves the adjoint equation, has minimum norm among all "
                        + "such solutions, and its squared norm equals the target quadratic "
                        + "form on the canonical Gram preimage. This is the target-specific "
                        + "condition cost without introducing a substitute pseudoinverse.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies adjoint-range duality, equality of the Gram and "
                        + "adjoint ranges, orthogonal decomposition, and Pythagoras. Repository "
                        + "searches found no existing theorem combining all public clauses."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("State");
        Formula observation = F.Id("Observation");
        Formula measurement = F.Id("M");
        Formula target = F.Id("v");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula stateCertificate = F.Id("s");
        Formula coefficient = F.Id("a");
        Formula candidate = F.Id("b");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula mapType = Call("LinearMap", scalar, state, observation);
        Formula pairType = Seq(state, Sp, Times, Sp, observation);
        Formula adjoint = Seq(measurement, Caret, Grp(Star));
        Formula kernelOrthogonal = Seq(
            Open, Ker, Open, measurement, Close, Close, Caret, Grp(Perp));
        Formula visibility = Seq(
            Forall, Sp, Typed(Seq(x, Comma, Sp, y), state), Comma, Sp,
            Call(measurement, x), Sp, Eq, Sp, Call(measurement, y), Sp,
            Rightarrow, Sp, Inner(target, x), Sp, Eq, Sp, Inner(target, y));
        Formula minimumNorm = Seq(
            Forall, Sp, Typed(candidate, observation), Comma, Sp,
            Call(adjoint, candidate), Sp, Eq, Sp, target, Sp, Rightarrow, Sp,
            new Formula.Norm(coefficient), Sp, Leq, Sp, new Formula.Norm(candidate));
        Formula cost = Seq(
            new Formula.Norm(coefficient), Caret, Grp(D(2)), Sp, Eq, Sp,
            Inner(target, stateCertificate));
        Formula certificate = Seq(
            Exists, Bang, Sp,
            Typed(OpenPair(stateCertificate, coefficient), pairType), Comma,
            RowBreak, Grp(),
            stateCertificate, Sp, InMacro, Sp, kernelOrthogonal, Sp, Land,
            RowBreak, Grp(),
            Call(adjoint, coefficient), Sp, Eq, Sp, target, Sp, Land,
            RowBreak, Grp(),
            coefficient, Sp, Eq, Sp, Call(measurement, stateCertificate), Sp, Land,
            RowBreak, Grp(),
            Open, minimumNorm, Close, Sp, Land,
            RowBreak, Grp(), cost);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(scalar, Comma, Sp, state, Comma, Sp, observation), type),
            Comma, RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", state), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land,
            RowBreak, Grp(),
            Call("NormedAddCommGroup", observation), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, observation), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, observation), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, Typed(measurement, mapType), Comma, Sp,
            Typed(target, state), Comma,
            RowBreak, Grp(),
            Open, visibility, Close, Sp, Iff, Sp, Open, certificate, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);

    private static Formula OpenPair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Call(Formula name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}

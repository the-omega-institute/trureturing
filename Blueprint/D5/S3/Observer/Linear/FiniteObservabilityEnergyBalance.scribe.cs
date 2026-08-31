using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class FiniteObservabilityEnergyBalanceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Linear/FiniteObservabilityEnergyBalance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite observability Gramian telescopes, is positive semidefinite, and measures "
            + "state energy loss.",
        H("Finite Observability Energy Balance"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-observability-energy-balance"),
            DeclarationHandle.Create(Prefix + "finite_observability_energy_balance"),
            H("Finite observability identity and energy balance"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The bounded update A and readout C act on complete inner-product spaces "
                        + "over a real or complex scalar field. The conservation law A* A + "
                        + "C* C = I is the source premise.")),
                Paragraph(Text(
                    "The finite Gramian is the explicit sum of the adjoint readout terms "
                        + "for k below N. The first public clause telescopes this sum against "
                        + "the N-step state operator.")),
                Paragraph(Text(
                    "The second clause states operator positivity, including symmetry and "
                        + "nonnegativity of every quadratic form. The third clause gives the "
                        + "corresponding finite state norm-energy balance.")),
                Paragraph(Text(
                    "Repository and pinned-library searches found no packaged theorem with "
                        + "all three clauses. The proof applies the adjoint-power law, finite "
                        + "sum telescoping, and adjoint inner-product identities directly."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula update = F.Id("A");
        Formula readout = F.Id("C");
        Formula horizon = F.Id("N");
        Formula point = F.Id("x");
        Formula index = F.Id("k");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula updateType = Call("ContinuousLinearMap", scalar, state, state);
        Formula readoutType = Call("ContinuousLinearMap", scalar, state, output);
        Formula updatePower = Seq(update, Caret, Grp(horizon));
        Formula updatePowerAdjoint = Seq(Call("adjoint", updatePower));
        Formula stepPower = Seq(update, Caret, Grp(index));
        Formula stepPowerAdjoint = Seq(Call("adjoint", stepPower));
        Formula readoutAdjoint = Call("adjoint", readout);
        Formula gramTerm = Seq(
            Open, stepPowerAdjoint, Sp, Circ, Sp,
            Open, readoutAdjoint, Sp, Circ, Sp, readout, Close, Sp, Circ, Sp,
            stepPower, Close);
        Formula gramian = Seq(
            Sum, Underscore, Grp(Seq(index, InMacro, Call("range", horizon))), Sp,
            gramTerm);
        Formula lhs = Seq(
            Call("id"), Sp, Minus, Sp,
            Open, updatePowerAdjoint, Sp, Circ, Sp, updatePower, Close);
        Formula conservation = Seq(
            Open, Call("adjoint", update), Sp, Circ, Sp, update, Close, Sp,
            Plus, Sp,
            Open, readoutAdjoint, Sp, Circ, Sp, readout, Close, Sp,
            Eq, Sp, Call("id"));
        Formula identity = Seq(lhs, Sp, Eq, Sp, gramian);
        Formula positivity = Call("IsPositive", gramian);
        Formula energy = Seq(
            new Formula.Norm(point), Caret, Grp(D(2)), Sp, Minus, Sp,
            new Formula.Norm(Seq(Open, updatePower, Sp, point, Close)), Caret, Grp(D(2)),
            Sp, Eq, Sp,
            Sum, Underscore, Grp(Seq(index, InMacro, Call("range", horizon))), Sp,
            new Formula.Norm(Seq(Open, readout, Sp, stepPower, Sp, point, Close)),
            Caret, Grp(D(2)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output,
                Colon, Sp, type, Comma),
            Seq(Grp(), Typeclass("RCLike", scalar), Sp, Land, Sp,
                Typeclass("NormedAddCommGroup", state), Sp, Land, Sp,
                Typeclass("InnerProductSpace", scalar, state), Sp, Land, Sp,
                Typeclass("CompleteSpace", state), Sp, Land),
            Seq(Grp(), Typeclass("NormedAddCommGroup", output), Sp, Land, Sp,
                Typeclass("InnerProductSpace", scalar, output), Sp, Land, Sp,
                Typeclass("CompleteSpace", output), Sp, Land),
            Seq(Forall, Sp, Typed(update, updateType), Comma, Sp,
                Typed(readout, readoutType), Comma, Sp,
                Typed(horizon, natural), Comma, Sp, conservation,
                Sp, Rightarrow, RowBreak, Grp()),
            Seq(Grp(), identity, Sp, Land, Sp, positivity, Sp, Land, Sp,
                Forall, Sp, Typed(point, state), Comma, Sp, energy, Dot)
        ]));
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
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}

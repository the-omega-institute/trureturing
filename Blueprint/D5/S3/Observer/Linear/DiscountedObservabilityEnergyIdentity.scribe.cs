using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DiscountedObservabilityEnergyIdentityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discounted observability Gramian quadratic form equals total discounted readout energy.",
        H("Discounted Observability Energy Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-observability-energy-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Linear/DiscountedObservabilityEnergyIdentity."
                        + "discounted_observability_energy_identity"),
                H("The Gramian quadratic form is total discounted readout energy"),
                StatementSource.FromAuthor(EnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. Construct the discounted observability "
                            + "Gramian from the evolution T and readout C using the canonical "
                            + "norm-convergent operator series.")),
                    Paragraph(Text(
                        "For positive beta under the stated square-root norm bound, the real "
                            + "part of its quadratic form at x is the infinite sum of beta to "
                            + "the nth power times the squared norm of the nth observed iterate.")),
                    Paragraph(Text(
                        "Continuous evaluation, inner product, and real-part maps transport the "
                            + "summable operator series term by term. The pinned library's "
                            + "adjoint-composition identity identifies each transported term "
                            + "with its squared readout norm.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no public packaged theorem "
                            + "for the complete identity. Existing canonical Gramian and iterate "
                            + "constructions are reused directly."))),
                DescribeRole.Theorem))));

    private static Formula EnergyFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula discount = Beta;
        Formula point = F.Id("x");
        Formula index = F.Id("n");
        Formula gramian = Call("discountedObservabilityGramian", evolution, readout, discount);
        Formula observed = Call("observedIterate", evolution, readout, index, point);
        Formula inner = Seq(Langle, Sp, point, Comma, Sp,
            Seq(gramian, Open, point, Close), Sp, Rangle);
        Formula energyTerm = Seq(
            discount, Caret, Grp(index), Sp,
            new Formula.Norm(observed), Caret, Grp(D(2)));
        Formula energy = Seq(
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp, energyTerm);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output, Comma,
            RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", state), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land,
            RowBreak, Grp(),
            Call("NormedAddCommGroup", output), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, output), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, output), Sp, Land,
            RowBreak, Grp(),
            evolution, Colon, Sp, Call("LinearMap", scalar, state, state), Comma, Sp,
            readout, Colon, Sp, Call("LinearMap", scalar, state, output), Comma, Sp,
            discount, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            point, InMacro, Sp, state, Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, discount, Sp, Land, Sp,
            Sqrt, Grp(discount), Sp, new Formula.Norm(evolution), Sp, Lt, Sp, D(1),
            Sp, Rightarrow,
            RowBreak, Grp(),
            Re, Open, inner, Close, Sp, Eq, Sp, energy, Dot));
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

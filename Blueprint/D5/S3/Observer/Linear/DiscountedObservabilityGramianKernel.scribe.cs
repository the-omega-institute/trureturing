using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DiscountedObservabilityGramianKernelDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discounted observability Gramian kernel is the all-future readout kernel.",
        H("Discounted Observability Gramian Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-observability-gramian-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Linear/DiscountedObservabilityGramianKernel."
                        + "discounted_observability_gramian_kernel"),
                H("The Gramian kernel is the all-future readout kernel"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. The evolution T and readout C are arbitrary "
                            + "linear maps, and beta satisfies the stated discount and norm "
                            + "convergence restrictions.")),
                    Paragraph(Text(
                        "The Gramian is the norm-convergent sum of the discounted adjoint Gram "
                            + "terms constructed in the positivity result. The right side is the "
                            + "canonical all-future readout kernel imported from the observer "
                            + "memory family.")),
                    Paragraph(Text(
                        "Each quadratic-form summand is beta to the nth power times the squared "
                            + "norm of the nth observed iterate. Since every term is nonnegative "
                            + "and beta is positive, zero total energy is equivalent to every "
                            + "future readout vanishing.")),
                    Paragraph(Text(
                        "Repository searches found no packaged Gramian-kernel theorem. The proof "
                            + "applies the pinned library's adjoint norm identity, transport of "
                            + "summable series through continuous maps, and strict positivity of "
                            + "a nonnegative series containing a positive term."))),
                DescribeRole.Theorem))));

    private static Formula KernelFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula discount = Beta;
        Formula index = F.Id("n");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula mapState = Call("LinearMap", scalar, state, state);
        Formula mapOutput = Call("LinearMap", scalar, state, output);
        Formula gramian = new Formula.Subscript(F.Id("W"), discount);
        Formula hidden = new Formula.Subscript(F.Id("N"), Infty);
        Formula evolutionAdjoint = Seq(evolution, Caret, Grp(Star));
        Formula readoutAdjoint = Seq(readout, Caret, Grp(Star));
        Formula summand = Seq(
            discount, Caret, Grp(index), Sp,
            evolutionAdjoint, Caret, Grp(index), Sp,
            readoutAdjoint, Sp, readout, Sp,
            evolution, Caret, Grp(index));
        Formula construction = Seq(
            gramian, Sp, Eq, Sp, Sum, Underscore, Grp(index, Eq, D(0)),
            Caret, Grp(Infty), Sp, summand);
        Formula convergence = Seq(
            D(0), Sp, Lt, Sp, discount, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Sqrt, Grp(discount), Sp, new Formula.Norm(evolution), Sp, Lt, Sp, D(1));
        Formula hiddenDefinition = Seq(
            hidden, Sp, Eq, Sp, Call("iInf", index,
                Call("ker", Seq(readout, Sp, Circ, Sp,
                    evolution, Caret, Grp(index)))));

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output, Colon, Sp, type,
            Comma, Sp, OpenBracket, Call("RCLike", scalar), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", state), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", scalar, state), CloseBracket, Comma, Sp,
            OpenBracket, Call("FiniteDimensional", scalar, state), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", output), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", scalar, output), CloseBracket, Comma, Sp,
            OpenBracket, Call("FiniteDimensional", scalar, output), CloseBracket, RowBreak, Grp(),
            evolution, Colon, Sp, mapState, Comma, Sp,
            readout, Colon, Sp, mapOutput, Comma, Sp,
            discount, Colon, Sp, real, Comma, RowBreak, Grp(),
            hiddenDefinition, Comma, RowBreak, Grp(),
            RowBreak, Grp(),
            convergence, Sp, Rightarrow,
            RowBreak, Grp(),
            construction, Sp, Land, Sp,
            Call("ker", gramian), Sp, Eq, Sp, hidden, Dot));
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

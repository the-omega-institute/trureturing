using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DiscountedObservabilityGramianPositivityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A convergent discounted observability Gramian is positive semidefinite.",
        H("Discounted Observability Gramian Positivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-observability-gramian-positivity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity."
                        + "discounted_observability_gramian_nonnegative"),
                H("The discounted observability Gramian is positive semidefinite"),
                StatementSource.FromAuthor(PositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. The evolution T and readout C are arbitrary "
                            + "linear maps on these source carriers.")),
                    Paragraph(Text(
                        "The Gramian is constructed as the norm-convergent infinite sum of the "
                            + "discounted adjoint Gram terms. Its public assumptions retain both "
                            + "the source discount range and the stated square-root norm bound.")),
                    Paragraph(Text(
                        "Each summand is a nonnegative real scalar multiple of an adjoint "
                            + "composition. A geometric majorant proves summability, and "
                            + "continuous evaluation, inner product, and real-part maps carry "
                            + "the operator sum to a sum of nonnegative quadratic forms.")),
                    Paragraph(Text(
                        "Repository searches found no existing discounted observability "
                            + "Gramian theorem. The proof directly applies the pinned library's "
                            + "adjoint-composition positivity, operator norm bounds, geometric "
                            + "summability, and infinite-sum transport lemmas."))),
                DescribeRole.Theorem))));

    private static Formula PositivityFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula discount = Beta;
        Formula index = F.Id("n");
        Formula gramian = new Formula.Subscript(F.Id("W"), discount);
        Formula evolutionAdjoint = Grp(evolution, Caret, Grp(Star));
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

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output, Comma, Sp,
            evolution, Comma, Sp, readout, Comma, Sp, discount, Comma,
            RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, output), Sp, Land,
            RowBreak, Grp(),
            convergence, Sp, Rightarrow,
            RowBreak, Grp(),
            construction, Sp, Land, Sp, D(0), Sp, Le, Sp, gramian, Dot));
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

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DiscountedObservabilityGramianEquationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discounted observability Gramian satisfies its Lyapunov equation.",
        H("Discounted Observability Gramian Equation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-observability-gramian-equation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Linear/DiscountedObservabilityGramianEquation."
                        + "discounted_observability_gramian_equation"),
                H("The discounted Gramian obeys the fixed-point equation"),
                StatementSource.FromAuthor(EquationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. The evolution T and readout C are arbitrary "
                            + "linear maps on these carriers.")),
                    Paragraph(Text(
                        "The discount beta lies strictly between zero and one, and the stated "
                            + "square-root norm bound makes the canonical discounted Gramian "
                            + "series summable.")),
                    Paragraph(Text(
                        "Splitting off the zeroth Gram term gives the adjoint square of C. "
                            + "Every successor term is beta times the preceding term conjugated "
                            + "by T, so continuity transports the remaining infinite sum through "
                            + "that sandwich map.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact equation theorem. "
                            + "The proof directly applies the existing summability result, the "
                            + "zeroth-term sum split, adjoint reversal, and infinite-sum transport."))),
                DescribeRole.Theorem))));

    private static Formula EquationFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula discount = Beta;
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula evolutionType = Call("LinearMap", scalar, state, state);
        Formula readoutType = Call("LinearMap", scalar, state, output);
        Formula gramian = Call("discountedObservabilityGramian", evolution, readout, discount);
        Formula evolutionAdjoint = Seq(evolution, Caret, Grp(Star));
        Formula readoutAdjoint = Seq(readout, Caret, Grp(Star));
        Formula convergence = Seq(
            D(0), Sp, Lt, Sp, discount, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Sqrt, Grp(discount), Sp, new Formula.Norm(evolution), Sp, Lt, Sp, D(1));
        Formula equation = Seq(
            gramian, Sp, Eq, Sp,
            readoutAdjoint, Sp, readout, Sp, Plus, Sp,
            discount, Sp, evolutionAdjoint, Sp, gramian, Sp, evolution);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output, Colon, Sp, type,
            Comma, Sp,
            RowBreak, Grp(),
            Typeclass("RCLike", scalar), Comma, Sp,
            Typeclass("NormedAddCommGroup", state), Comma, Sp,
            Typeclass("InnerProductSpace", scalar, state), Comma, Sp,
            Typeclass("FiniteDimensional", scalar, state), Comma, RowBreak, Grp(),
            Typeclass("NormedAddCommGroup", output), Comma, Sp,
            Typeclass("InnerProductSpace", scalar, output), Comma, Sp,
            Typeclass("FiniteDimensional", scalar, output), Comma, RowBreak, Grp(),
            evolution, Colon, Sp, evolutionType, Comma, Sp,
            readout, Colon, Sp, readoutType, Comma, Sp,
            discount, Colon, Sp, real, Comma, RowBreak, Grp(),
            convergence, Sp, Rightarrow,
            RowBreak, Grp(),
            equation, Dot,
            End, Grp(F.Id("gathered"))));
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

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);
}

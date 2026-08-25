using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class FutureReadoutQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-future kernel quotient is the coarsest linear future-readout quotient "
            + "and carries unique induced dynamics.",
        H("Future Readout Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("future-readout-quotient-universality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/FutureReadoutQuotient."
                        + "future_readout_quotient_is_coarsest_with_unique_dynamics"),
                H("The future-readout quotient is coarsest and has unique dynamics"),
                StatementSource.FromAuthor(QuotientFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. A linear map T evolves V, and a linear map "
                            + "C supplies each readout.")),
                    Paragraph(Text(
                        "The hidden subspace is constructed from the source semantics as the "
                            + "intersection of the kernels of C after every forward power of T. "
                            + "Every future readout therefore descends through its canonical "
                            + "linear quotient.")),
                    Paragraph(Text(
                        "For any linear summary that determines all of those future readouts, "
                            + "the canonical quotient projection factors uniquely through the "
                            + "summary's effective range. This is the public universal property "
                            + "expressing that the quotient is coarsest.")),
                    Paragraph(Text(
                        "Invariance of the all-future kernel under T makes T descend to the "
                            + "quotient. Surjectivity of the canonical quotient projection then "
                            + "forces that induced linear dynamics to be unique."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula QuotientFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula quotientType = F.Id("Q");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula index = F.Id("k");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula hidden = new Formula.Subscript(F.Id("N"), Infty);
        Formula quotient = Call("Quotient", state, hidden);
        Formula projection = Call("mkQ", hidden);
        Formula iterate = Seq(evolution, Caret, Grp(index));
        Formula futureAtX = Apply(readout, Apply(iterate, x));
        Formula futureAtY = Apply(readout, Apply(iterate, y));
        Formula construction = Call(
            "iInf", index, Call("ker", Seq(readout, Sp, Circ, Sp, iterate)));

        Formula descendedReadout = F.Id("Cbar");
        Formula descendedAtIndex = new Formula.Subscript(descendedReadout, index);
        Formula preservesFuture = Seq(
            Exists, Sp,
            Typed(descendedReadout,
                Arrow(F.Id("Nat"), Call("LinearMap", scalar, quotient, output))),
            Comma, RowBreak, Grp(),
            Forall, Sp, Typed(index, F.Id("Nat")), Comma, Sp,
            Typed(x, state), Comma, Sp,
            Apply(descendedAtIndex, Apply(projection, x)), Sp, Eq, Sp, futureAtX);

        Formula summary = F.Id("q");
        Formula factor = F.Id("Phi");
        Formula determinesFuture = Seq(
            Forall, Sp, Typed(x, state), Comma, Sp, Typed(y, state), Comma, Sp,
            Apply(summary, x), Sp, Eq, Sp, Apply(summary, y), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, Typed(index, F.Id("Nat")), Comma, Sp,
            futureAtX, Sp, Eq, Sp, futureAtY);
        Formula coarsest = Seq(
            Forall, Sp, Typed(quotientType, type), Comma, RowBreak, Grp(),
            Open, Call("AddCommGroup", quotientType), Sp, Land, Sp,
            Call("Module", scalar, quotientType), Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp,
            Typed(summary, Call("LinearMap", scalar, state, quotientType)), Comma,
            RowBreak, Grp(), Open, determinesFuture, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Exists, Bang, Sp,
            Typed(factor,
                Call("LinearMap", scalar, Call("range", summary), quotient)),
            Comma, Sp, projection, Sp, Eq, Sp, factor, Sp, Circ, Sp,
            Call("rangeRestrict", summary));

        Formula induced = F.Id("Tbar");
        Formula uniqueDynamics = Seq(
            Exists, Bang, Sp,
            Typed(induced, Call("LinearMap", scalar, quotient, quotient)), Comma,
            RowBreak, Grp(),
            Forall, Sp, Typed(x, state), Comma, Sp,
            Apply(induced, Apply(projection, x)), Sp, Eq, Sp,
            Apply(projection, Apply(evolution, x)));

        Formula carrierStructures = Seq(
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", state), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land,
            RowBreak, Grp(),
            Call("NormedAddCommGroup", output), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, output), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, output));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(scalar, type), Comma, Sp, Typed(state, type), Comma, Sp,
            Typed(output, type), Comma, RowBreak, Grp(),
            Typed(evolution, Call("LinearMap", scalar, state, state)), Comma, Sp,
            Typed(readout, Call("LinearMap", scalar, state, output)), Comma,
            RowBreak, Grp(), Open, carrierStructures, Close, Sp, Rightarrow,
            RowBreak, Grp(), hidden, Sp, Colon, Eq, Sp, construction, Semi,
            RowBreak, Grp(), Open, preservesFuture, Close, Sp, Land,
            RowBreak, Grp(), Open, coarsest, Close, Sp, Land,
            RowBreak, Grp(), Open, uniqueDynamics, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

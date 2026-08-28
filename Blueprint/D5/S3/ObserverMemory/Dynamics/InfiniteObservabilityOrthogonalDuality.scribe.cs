using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class InfiniteObservabilityOrthogonalDualityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-future readout kernel is the orthogonal complement of the observable orbit.",
        H("Infinite Observability Orthogonal Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("infinite-observability-orthogonal-duality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality."
                        + "infinite_unobservable_eq_observable_orthogonal"),
                H("The infinite hidden and observable spaces are orthogonal duals"),
                StatementSource.FromAuthor(DualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. Let T evolve V linearly and let C read V "
                            + "linearly into Y.")),
                    Paragraph(Text(
                        "The hidden space is constructed from the kernels of C composed with "
                            + "every nonnegative power of T. Independently, the observable space "
                            + "is the span of every vector obtained by applying an adjoint power "
                            + "of T to a vector in the adjoint image of C.")),
                    Paragraph(Text(
                        "The public equality states that the all-future hidden space is exactly "
                            + "the orthogonal complement of that observable span. Each side is "
                            + "therefore determined by the source dynamics and readout before "
                            + "the equality is proved.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no packaged theorem with "
                            + "this full statement. The proof applies the library's adjoint inner-"
                            + "product identity and span induction in both directions."))),
                DescribeRole.Theorem))));

    private static Formula DualityFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula index = F.Id("k");
        Formula value = F.Id("y");
        Formula hidden = new Formula.Subscript(F.Id("N"), Infty);
        Formula observable = new Formula.Subscript(F.Id("O"), Infty);
        Formula iterate = Seq(evolution, Caret, Grp(index));
        Formula adjointEvolution = Grp(evolution, Caret, Grp(Star));
        Formula adjointReadout = Seq(readout, Caret, Grp(Star));
        Formula futureReadout = Seq(readout, Sp, Circ, Sp, iterate);
        Formula hiddenConstruction = Call("iInf", index, Call("ker", futureReadout));
        Formula generator = Seq(
            adjointEvolution, Caret, Grp(index), Open,
            adjointReadout, Open, value, Close, Close);
        Formula observableConstruction = Call(
            "span",
            scalar,
            Seq(OpenBrace, generator, Sp, Mid, Sp,
                index, Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
                value, Sp, InMacro, Sp, output, CloseBrace));
        Formula orthogonal = Seq(observable, Caret, Grp(Perp));

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output,
            Comma, Sp, evolution, Comma, Sp, readout, Comma,
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
            evolution, Sp, InMacro, Sp, Call("LinearMap", scalar, state, state), Sp,
            Land, Sp,
            readout, Sp, InMacro, Sp, Call("LinearMap", scalar, state, output), Sp,
            Rightarrow,
            RowBreak, Grp(),
            hidden, Sp, Colon, Eq, Sp, hiddenConstruction, Semi, Sp,
            observable, Sp, Colon, Eq, Sp, observableConstruction, Semi,
            RowBreak, Grp(),
            hidden, Sp, Eq, Sp, orthogonal, Dot));
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

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class FiniteObservabilityOrthogonalDualityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each finite readout kernel is the orthogonal complement of its observable Krylov space.",
        H("Finite Observability Orthogonal Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-observability-orthogonal-duality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/FiniteObservabilityOrthogonalDuality."
                        + "finite_unobservable_eq_observable_orthogonal"),
                H("Finite hidden and observable spaces are orthogonal duals"),
                StatementSource.FromAuthor(DualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V and Y be finite-dimensional inner-product spaces over a real or "
                            + "complex scalar field. Let T evolve V linearly, let C read V "
                            + "linearly into Y, and fix a nonnegative depth m.")),
                    Paragraph(Text(
                        "The finite hidden space intersects the kernels of C composed with T to "
                            + "the kth power for every k at most m. The finite observable space "
                            + "uses the family's canonical observableKrylov construction: the "
                            + "span of the matching adjoint-orbit vectors.")),
                    Paragraph(Text(
                        "The sole public conclusion identifies the hidden space with the "
                            + "orthogonal complement of that independently constructed visible "
                            + "space. It applies uniformly at every finite depth.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no packaged finite-depth "
                            + "duality theorem. The proof directly applies the adjoint inner-"
                            + "product identity and span induction in both directions."))),
                DescribeRole.Theorem))));

    private static Formula DualityFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula depth = F.Id("m");
        Formula index = F.Id("k");
        Formula value = F.Id("y");
        Formula hidden = new Formula.Subscript(F.Id("N"), depth);
        Formula observable = new Formula.Subscript(F.Id("O"), depth);
        Formula iterate = Seq(evolution, Caret, Grp(index));
        Formula adjointEvolution = Grp(evolution, Caret, Grp(Star));
        Formula adjointReadout = Seq(readout, Caret, Grp(Star));
        Formula futureReadout = Seq(readout, Sp, Circ, Sp, iterate);
        Formula hiddenConstruction = Call(
            "iInf",
            Seq(D(0), Sp, Le, Sp, index, Sp, Le, Sp, depth),
            Call("ker", futureReadout));
        Formula generator = Seq(
            adjointEvolution, Caret, Grp(index), Open,
            adjointReadout, Open, value, Close, Close);
        Formula observableConstruction = Call(
            "span",
            scalar,
            Seq(OpenBrace, generator, Sp, Mid, Sp,
                D(0), Sp, Le, Sp, index, Sp, Le, Sp, depth,
                Comma, Sp, value, Sp, InMacro, Sp, output, CloseBrace));
        Formula orthogonal = Seq(observable, Caret, Grp(Perp));

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output,
            Comma, Sp, evolution, Comma, Sp, readout, Comma, Sp, depth, Comma,
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
            Land, Sp, depth, Sp, InMacro, Sp, F.Id("N"), Sp, Rightarrow,
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

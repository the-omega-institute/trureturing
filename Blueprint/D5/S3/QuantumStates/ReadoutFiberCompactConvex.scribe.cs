using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class ReadoutFiberCompactConvexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty finite-dimensional positive readout fiber is compact and convex.",
        H("Compact Convex Readout Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonempty-positive-readout-fiber-is-compact-convex"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/ReadoutFiberCompactConvex."
                        + "readout_fiber_compact_convex"),
                H("Nonempty positive readout fibers are compact and convex"),
                StatementSource.FromAuthor(FiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The fiber is built from the source primitives: a finite-dimensional "
                            + "complex matrix state, a linear readout, positivity, and trace-one "
                            + "normalization. A nonempty fiber has a witness state, so its "
                            + "arbitrary readout value agrees with the frozen physical-fiber "
                            + "construction.")),
                    Paragraph(Text(
                        "The compactness and convexity clauses are discharged by the existing "
                            + "repository theorem D5/S3/Quantum/Fibers/PhysicalFiber."
                            + " The new statement only transports that theorem from a witness "
                            + "readout value to an arbitrary nonempty fiber."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula LinearMap(Formula scalar, Formula source, Formula target) =>
        Seq(Operatorname, Grp(F.Id("LinearMap")), Underscore, Grp(scalar),
            Open, source, Sp, To, Sp, target, Close);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula FiberFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula readout = F.Id("readout");
        Formula y = F.Id("y");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula state = Call("Matrix", n, n, complex);
        Formula output = Seq(k, Sp, To, Sp, complex);
        Formula readoutType = LinearMap(complex, state, output);
        Formula fiber = Call("readoutFiber", readout, y);

        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, k, Comma, Sp,
            Typeclass("Fintype", n), Comma, Sp,
            Typeclass("Nonempty", n), Comma, Sp,
            Typeclass("Finite", k), Comma, Esc,
            readout, Colon, Sp, readoutType, Comma, Sp,
            y, Colon, Sp, output, Comma, Esc,
            Call("Nonempty", fiber), Sp,
            Rightarrow, Sp,
            Call("IsCompact", fiber), Sp,
            Land, Sp,
            Call("Convex", Seq(Mathbb, Grp(F.Id("R"))), fiber), Dot));
    }
}

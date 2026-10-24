using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class FiniteTimeTomographySaturationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-future observability is decided by the first trace-zero carrier dimension layers.",
        H("Finite-Time Tomography Saturation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-future-kernel-finrank-truncation"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation."
                        + "all_future_kernel_eq_finrank_kernel"),
                H("The ambient dimension truncates the future kernel"),
                StatementSource.FromAuthor(GeneralSaturationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite-dimensional module V over any field K, an endomorphism A "
                        + "and a linear readout C into any K-module Y, the intersection of "
                        + "all future kernels equals the intersection indexed by "
                        + "Fin(finrank K V). The zero-dimensional case is included. "
                        + "This general statement also applies to complex structural "
                        + "Hilbert spaces with their classicality-defect readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-time-tomography-saturation"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation."
                        + "finite_time_tomography_saturation"),
                H("The exact trace-zero dimension controls every future readout"),
                StatementSource.FromAuthor(SaturationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive matrix dimension d. The state carrier is the imported "
                            + "real subspace HermitianTraceZero(Fin d), the evolution A is a "
                            + "real-linear endomorphism of that carrier, and C is a real-linear "
                            + "readout into an arbitrary real module Y.")),
                    Paragraph(Text(
                        "The all-future kernel is constructed by intersecting ker(C composed "
                            + "with A to the kth power) over every natural k. The finite kernel "
                            + "uses the same source test over the exact index type Fin(d squared "
                            + "minus one).")),
                    Paragraph(Text(
                        "The public statement contains both source clauses: a trivial all-future "
                            + "kernel forces the finite kernel to be trivial, and more strongly "
                            + "the two constructed kernels are equal.")),
                    Paragraph(Text(
                        "The proof applies Cayley--Hamilton polynomial reduction to express every "
                            + "later evolution power through the first ambient-finrank powers. "
                            + "The imported finrank theorem identifies that ambient real dimension "
                            + "as d squared minus one."))),
                DescribeRole.Theorem))));

    private static Formula GeneralSaturationFormula()
    {
        Formula field = F.Id("K");
        Formula space = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("A");
        Formula readout = F.Id("C");
        Formula index = F.Id("k");
        Formula kernel = Call("ker", Seq(readout, Sp, Circ, Sp,
            evolution, Caret, Grp(index)));
        return Disp(Seq(
            Forall, Sp, field, Comma, Sp, space, Comma, Sp, output,
            Colon, Sp, F.Id("Type"), Comma,
            Call("Field", field), Sp, Land, Sp,
            Call("AddCommGroup", space), Sp, Land, Sp,
            Call("Module", field, space), Sp, Land, Sp,
            Call("FiniteDimensional", field, space), Sp, Land, Sp,
            Call("AddCommGroup", output), Sp, Land, Sp,
            Call("Module", field, output), Sp, Rightarrow,
            RowBreak, Grp(), Forall, Sp,
            evolution, Colon, Sp, Call("LinearMap", field, space, space), Comma, Sp,
            readout, Colon, Sp, Call("LinearMap", field, space, output), Comma,
            RowBreak, Grp(),
            Call("iInf", Seq(index, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N"))), kernel),
            Sp, Eq, Sp,
            Call("iInf", Seq(index, Sp, InMacro, Sp,
                Call("Fin", Call("finrank", field, space))), kernel), Dot));
    }

    private static Formula SaturationFormula()
    {
        Formula d = F.Id("d");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("A");
        Formula readout = F.Id("C");
        Formula index = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula horizon = Seq(d, Caret, Grp(D(2)), Sp, Minus, Sp, D(1));
        Formula carrier = Call("HermitianTraceZero", Call("Fin", d));
        Formula iterate = Seq(evolution, Caret, Grp(index));
        Formula futureReadout = Seq(readout, Sp, Circ, Sp, iterate);
        Formula kernel = Call("ker", futureReadout);
        Formula infiniteKernel = new Formula.Subscript(F.Id("N"), Infty);
        Formula finiteKernel = new Formula.Subscript(F.Id("N"), horizon);
        Formula infiniteConstruction = Call(
            "iInf", Seq(index, Sp, InMacro, Sp, naturals), kernel);
        Formula finiteConstruction = Call(
            "iInf", Seq(index, Sp, InMacro, Sp, Call("Fin", horizon)), kernel);
        Formula bottom = Call("bot");
        Formula finiteImplication = Seq(
            Open, infiniteKernel, Sp, Eq, Sp, bottom, Sp, Rightarrow, Sp,
            finiteKernel, Sp, Eq, Sp, bottom, Close);

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, Sp,
            output, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Call("AddCommGroup", output), Sp, Land, Sp,
            Call("Module", reals, output), Comma,
            RowBreak, Grp(),
            evolution, Colon, Sp, Call("LinearMap", reals, carrier, carrier), Comma, Sp,
            readout, Colon, Sp, Call("LinearMap", reals, carrier, output), Sp,
            Rightarrow,
            RowBreak, Grp(),
            infiniteKernel, Sp, Colon, Eq, Sp, infiniteConstruction, Semi, Sp,
            finiteKernel, Sp, Colon, Eq, Sp, finiteConstruction, Semi,
            RowBreak, Grp(),
            finiteImplication, Sp, Land, Sp,
            infiniteKernel, Sp, Eq, Sp, finiteKernel, Dot));
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

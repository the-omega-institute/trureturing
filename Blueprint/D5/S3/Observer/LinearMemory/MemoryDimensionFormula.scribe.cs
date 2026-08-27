using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class MemoryDimensionFormulaDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/MemoryDimensionFormula.memory_dimension_formula";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical linear memory quotient has dimension equal to the all-future "
            + "observable dimension minus the current readout rank.",
        H("Memory Dimension Formula"),
        Blocks(Describe.Lean(
            DescribeId.Create("memory-dimension-formula"),
            DeclarationHandle.Create(Declaration),
            H("Memory dimension is future visibility beyond current rank"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let V and Y be finite-dimensional inner-product spaces over a real or "
                        + "complex scalar field. Let T evolve V linearly and let C read V "
                        + "linearly into Y.")),
                Paragraph(Text(
                    "The memory object is the canonical quotient of the current kernel by "
                        + "the all-future kernel. The observable space is independently "
                        + "constructed as the span of every adjoint-observable iterate.")),
                Paragraph(Text(
                    "Quotient dimension, the imported orthogonal duality between the "
                        + "all-future kernel and observable span, and rank-nullity reduce both "
                        + "sides to the same finite-dimensional subtraction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula index = F.Id("k");
        Formula value = F.Id("y");
        Formula adjointEvolution = Seq(evolution, Caret, Grp(Star));
        Formula adjointReadout = Seq(readout, Caret, Grp(Star));
        Formula generator = Seq(
            adjointEvolution, Caret, Grp(index), Open,
            adjointReadout, Open, value, Close, Close);
        Formula observable = Call(
            "span",
            scalar,
            Seq(OpenBrace, generator, Sp, Mid, Sp,
                index, Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
                value, Sp, InMacro, Sp, output, CloseBrace));
        Formula memory = Call("memoryQuotient", readout, evolution);
        Formula equation = new Formula.Relation(
            Call("finrank", scalar, memory),
            FormulaRelationOperator.Equal,
            Subtract(
                Call("finrank", scalar, observable),
                Call("finrank", scalar, Call("range", readout))));

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
            equation, Dot));
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

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class PhysicalFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-dimensional physical readout fiber is nonempty, compact, and convex.",
        H("Finite-Dimensional Physical Fiber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-dimensional-physical-fibers-are-nonempty-compact-convex"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/PhysicalFiber.finite_dimensional_physical_fiber"),
                H("Finite-dimensional physical fibers are nonempty, compact, and convex"),
                StatementSource.FromAuthor(PhysicalFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a finite-dimensional complex matrix algebra, a positive "
                            + "trace-one state rho, and a finite family of accessible linear "
                            + "readouts. The physical fiber consists exactly of positive "
                            + "trace-one matrices whose accessible readout equals that of rho.")),
                    Paragraph(Text(
                        "The fiber contains rho. It is closed because the readout equality, "
                            + "positive cone, and trace-one slice are closed, and it lies in "
                            + "the compact unit ball because a positive trace-one matrix has "
                            + "operator norm at most one.")),
                    Paragraph(Text(
                        "Linearity preserves the fixed readout and trace under convex mixtures, "
                            + "while positive semidefiniteness is closed under nonnegative sums. "
                            + "Thus the same constructed fiber satisfies all three clauses."))),
                DescribeRole.Theorem))));

    private static Formula PhysicalFiberFormula()
    {
        Formula fiber = Seq(
            Operatorname, Grp(F.Id("PhysFiber")), Underscore, Grp(F.Id("O")),
            Open, Rho, Close);

        return Disp(Seq(
            fiber, Sp, Neq, Sp, Emptyset, Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("IsCompact")), Open, fiber, Close, Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("Convex")), Underscore,
            Grp(Mathbb, Grp(F.Id("R"))), Open, fiber, Close, Dot));
    }
}

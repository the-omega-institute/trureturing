using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class FiniteExpectationTableSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unrealizable complete affine expectation table has a finite linear certificate.",
        H("Finite Expectation Table Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-expectation-table-separation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MeasureSeparation/FiniteExpectationTableSeparation."
                        + "finite_expectation_table_separation"),
                H("A finite linear inequality detects nonrealizability"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The density-matrix carrier is exposed as a compact convex subset of a "
                            + "real normed state space. Every effect expectation is a continuous "
                            + "affine real-valued map, and the complete formal table is assumed "
                            + "not to agree with any state on every effect.")),
                    Paragraph(Text(
                        "The open sets on which one effect disagrees with the table cover the "
                            + "density matrices. Compactness extracts a finite effect set. Its "
                            + "finite readout image is compact and convex.")),
                    Paragraph(Text(
                        "Finite-dimensional Hahn-Banach separation supplies a continuous linear "
                            + "functional and threshold. Every realizable selected readout lies "
                            + "strictly below the threshold, while the selected entries of the "
                            + "formal table lie strictly above it."))),
                DescribeRole.Theorem))));

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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula protocol = F.Id("Protocol");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula density = F.Id("D");
        Formula expectation = F.Id("e");
        Formula table = F.Id("y");
        Formula selected = F.Id("S");
        Formula witness = F.Id("L");
        Formula threshold = F.Id("a");
        Formula rho = Rho;
        Formula effect = F.Id("p");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula selectedReadout = Seq(
            Open, effect, Colon, Sp, selected, Sp, Mapsto, Sp,
            Apply(expectation, effect, rho), Close);
        Formula selectedTable = Seq(
            Open, effect, Colon, Sp, selected, Sp, Mapsto, Sp,
            Apply(table, effect), Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(state, type), Comma, Sp,
                Typed(protocol, type), Comma),
            Seq(
                Call("NormedAddCommGroup", state), Sp, Land, Sp,
                Call("NormedSpace", real, state), Comma),
            Seq(
                Typed(density, Call("Set", state)), Comma, Sp,
                Typed(expectation, Arrow(protocol, Call("ContinuousAffineMap", real, state, real))),
                Comma),
            Seq(
                Typed(table, Arrow(protocol, real)), Comma, Sp,
                Call("IsCompact", density), Sp, Land, Sp,
                Call("Convex", real, density), Comma),
            Seq(
                Neg, Exists, Sp, Typed(rho, state), Comma, Sp,
                rho, InMacro, Sp, density, Sp, Land, Sp,
                Forall, Sp, Typed(effect, protocol), Comma, Sp,
                Apply(expectation, effect, rho), Sp, Eq, Sp, Apply(table, effect)),
            Seq(
                Rightarrow, Sp, Exists, Sp, Typed(selected, Call("Finset", protocol)), Comma, Sp,
                Typed(witness, Call("ContinuousLinearMap", real,
                    Arrow(selected, real), real)), Comma, Sp,
                Typed(threshold, real), Comma),
            Seq(
                Open, Forall, Sp, Typed(rho, state), Comma, Sp,
                rho, InMacro, Sp, density, Sp, Rightarrow, Sp,
                Apply(witness, selectedReadout), Sp, Lt, Sp, threshold, Close, Sp, Land),
            Seq(
                threshold, Sp, Lt, Sp, Apply(witness, selectedTable), Dot),
        ]));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ProductDynamicsLocalSupportDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Dynamics/ProductDynamicsLocalSupport."
            + "product_pullback_local_support";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Product pullbacks preserve exact local support or lower it within the active factors.",
        H("Product Dynamics Local Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("product-dynamics-local-support"),
                DeclarationHandle.Create(Declaration),
                H("Product pullbacks cannot create support outside the active set"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A normalized identity direction and a local trace map construct the "
                            + "scalar sector U as its real span and the trace-zero sector Z as "
                            + "the trace kernel. No abstract sector decomposition is assumed.")),
                    Paragraph(Text(
                        "The dynamics is the canonical tensor map induced by the local linear "
                            + "pullbacks. Scalar-sector invariance prevents a new active factor; "
                            + "multilinearity expands every active local sum over subsets of S.")),
                    Paragraph(Text(
                        "If the local pullbacks also preserve every Z sector, the same restriction "
                            + "map factors the product pullback through the original sector V(S)."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

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

    private static Formula TheoremFormula()
    {
        Formula iota = Iota, index = F.Id("i"), modules = F.Id("M");
        Formula scalar = Seq(Mathbb, Grp(F.Id("R")));
        Formula local = Apply(modules, index);
        Formula scalarSector = F.Id("U"), zeroSector = F.Id("Z");
        Formula unit = F.Id("I"), trace = F.Id("tr");
        Formula support = F.Id("S"), subset = F.Id("T"), set = F.Id("R");
        Formula dynamics = F.Id("phi"), observable = F.Id("A");
        Formula type = Call("Type");
        Formula moduleFamily = new Formula.TypeArrow(iota, type);
        Formula submoduleFamily = Seq(
            Prod, Underscore, Grp(index, Colon, Sp, iota), Sp,
            Call("Submodule", scalar, local));
        Formula mapFamily = Seq(
            Prod, Underscore, Grp(index, Colon, Sp, iota), Sp,
            Call("LinearMap", scalar, local, local));
        Formula unitFamily = Seq(
            Prod, Underscore, Grp(index, Colon, Sp, iota), Sp, local);
        Formula traceFamily = Seq(
            Prod, Underscore, Grp(index, Colon, Sp, iota), Sp,
            Call("LinearMap", scalar, local, scalar));
        Formula tensorSpace = Call("PiTensorProduct", scalar, modules);

        Formula Sector(Formula set) => Apply(F.Id("V"), set);
        Formula FactorFamily(Formula set) => Call(
            "factorFamily", Seq(index, Sp, Mapsto, Sp,
                Call("ifMem", index, set, Apply(zeroSector, index),
                    Apply(scalarSector, index))));
        Formula sectorDefinition = Seq(
            F.Id("V"), Colon, Sp,
            new Formula.TypeArrow(Call("Finset", iota),
                Call("Submodule", scalar, tensorSpace)), Sp, Colon, Eq, Sp,
            set, Sp, Mapsto, Sp,
            Call("range", Call("PiTensorMapIncl", scalar, FactorFamily(set))));
        Formula scalarDefinition = Seq(
            scalarSector, Colon, Sp, submoduleFamily, Sp, Colon, Eq, Sp,
            index, Sp, Mapsto, Sp,
            Call("span", scalar, Seq(OpenBrace, Apply(unit, index), CloseBrace)));
        Formula zeroDefinition = Seq(
            zeroSector, Colon, Sp, submoduleFamily, Sp, Colon, Eq, Sp,
            index, Sp, Mapsto, Sp, Call("ker", Apply(trace, index)));
        Formula pullback = F.Id("pullback");
        Formula pullbackDefinition = Seq(
            pullback, Colon, Sp, Call("LinearMap", scalar, tensorSpace, tensorSpace),
            Sp, Colon, Eq, Sp, Call("PiTensorMap", scalar, dynamics));
        Formula MapsInto(Formula family) => Seq(
            Call("map", Apply(dynamics, index), Apply(family, index)),
            Sp, Subseteq, Sp, Apply(family, index));
        Formula lowerSupport = Call(
            "iSup",
            Seq(OpenBrace, subset, Colon, Sp, Call("Finset", iota), Sp,
                Mid, Sp, subset, Sp, Subseteq, Sp, support, CloseBrace),
            Seq(subset, Sp, Mapsto, Sp, Sector(subset)));
        Formula sectorMembership = Seq(
            observable, Sp, InMacro, Sp, Sector(support));
        Formula mappedMembership(Formula target) => Seq(
            Apply(pullback, observable), Sp, InMacro, Sp, target);
        Formula firstClause = Seq(
            Forall, Sp, observable, Colon, Sp, tensorSpace, Comma, Sp,
            sectorMembership, Sp, Rightarrow, Sp, mappedMembership(lowerSupport));
        Formula exactClause = Seq(
            Forall, Sp, observable, Colon, Sp, tensorSpace, Comma, Sp,
            sectorMembership, Sp, Rightarrow, Sp, mappedMembership(Sector(support)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, iota, Colon, Sp, type, Comma, Sp,
            Call("DecidableEq", iota), Comma, RowBreak, Grp(),
            modules, Colon, Sp, moduleFamily, Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Colon, Sp, iota, Comma, Sp,
            Call("AddCommGroup", local), Sp, Land, Sp,
            Call("Module", scalar, local), Close, Comma, RowBreak, Grp(),
            unit, Colon, Sp, unitFamily, Comma, Sp,
            trace, Colon, Sp, traceFamily, Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Colon, Sp, iota, Comma, Sp,
            Apply(Apply(trace, index), Apply(unit, index)), Sp, Eq, Sp, D(1),
            Close, Comma, RowBreak, Grp(),
            dynamics, Colon, Sp, mapFamily, Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Colon, Sp, iota, Comma, Sp,
            Apply(Apply(dynamics, index), Apply(unit, index)), Sp, Eq, Sp,
            Apply(unit, index), Close, Comma, RowBreak, Grp(),
            support, Colon, Sp, Call("Finset", iota), Comma, RowBreak, Grp(),
            F.Text, Grp(F.Id("let"), Sp), Sp,
            scalarDefinition, Semi, RowBreak, Grp(),
            zeroDefinition, Semi, RowBreak, Grp(),
            sectorDefinition, Semi, RowBreak, Grp(),
            pullbackDefinition, Semi, RowBreak, Grp(),
            Open, firstClause, Close, Sp, Land, RowBreak, Grp(),
            Open, Open, Forall, Sp, index, Colon, Sp, iota, Comma, Sp,
            MapsInto(zeroSector), Close, Sp, Rightarrow, RowBreak, Grp(),
            exactClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

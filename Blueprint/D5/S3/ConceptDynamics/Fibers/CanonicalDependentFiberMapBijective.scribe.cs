using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class CanonicalDependentFiberMapBijectiveDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberMapBijective."
            + "canonical_dependent_fiber_map_bijective";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical map into the dependent sum of readout fibers is bijective.",
        H("Canonical Dependent Fiber Map Bijective"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-dependent-fiber-map-bijective"),
            DeclarationHandle.Create(Declaration),
            H("The canonical dependent-fiber map is bijective"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For any readout q : X -> B, the map records q(x), the object x, "
                        + "and the reflexive proof that x belongs to that fiber.")),
                Paragraph(Text(
                    "The frozen family equivalence supplies both injectivity and "
                        + "surjectivity without a quotient, section, or choice hypothesis."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula coordinate = F.Id("b");
        Formula point = F.Id("x");
        Formula fiberPoint = F.Id("y");
        Formula readout = F.Id("q");
        Formula fiber = Seq(
            Sum, Sp, Underscore, Grp(fiberPoint, Colon, Sp, source), Sp,
            Apply(readout, fiberPoint), Sp, Eq, Sp, coordinate);
        Formula totalFiber = Seq(
            Sum, Sp, Underscore, Grp(coordinate, Colon, Sp, coordinateType), Sp,
            fiber);
        Formula canonicalValue = Seq(
            Langle, Sp, Apply(readout, point), Comma, Sp,
            Langle, Sp, point, Comma, Sp, F.Id("refl"), Rangle, Rangle);
        Formula canonicalMap = Seq(
            point, Sp, Mapsto, Sp, canonicalValue,
            Colon, Sp, source, Sp, To, Sp, totalFiber);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coordinateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, source, Sp, To, Sp, coordinateType, Comma, Sp,
            Call("Bijective", canonicalMap), Dot));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

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

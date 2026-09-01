using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ToroidalObserverSetCoverDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/Adelic/ToroidalObserverSetCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-cost toroidal observers on a spectral window form a weighted set-cover "
            + "problem over their nonvanishing regions.",
        H("Toroidal Observer Design as Weighted Set Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("toroidal-observer-design-is-weighted-set-cover"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "toroidal_observer_design_is_weighted_set_cover"),
                H("Toroidal observer design is weighted set cover"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source does not construct the completed quadratic L-functions, "
                            + "so the Lean design accepts the twist family as an abstract "
                            + "parameter. Its visible region is the existing canonical "
                            + "nonvanishingDomain, and every observer cost is strictly positive.")),
                    Paragraph(Text(
                        "A finite selection is feasible exactly when the ambient compact-window "
                            + "set K is contained in the union of its nonzero-twist regions. The "
                            + "objective is the extended-real infimum of the corresponding finite "
                            + "cost sums; an absent finite cover therefore retains value top.")),
                    Paragraph(Text(
                        "The definition is realizable rather than vacuous: on the one-element "
                            + "index type, the constant twist one with cost one covers the whole "
                            + "complex plane by its singleton selection, with total cost one.")),
                    Paragraph(Text(
                        "No identification of the cost with torus length, log discriminant, or "
                            + "conductor is asserted, and no optimality claim for discriminant "
                            + "five is formalized; the source supplies neither definitions nor "
                            + "proofs for those stronger clauses."))),
                DescribeRole.Theorem))));

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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula extendedReal = Call("EReal");
        Formula indexType = F.Id("I");
        Formula design = F.Id("d");
        Formula window = F.Id("K");
        Formula selected = F.Id("F");
        Formula observer = F.Id("i");
        Formula point = F.Id("s");
        Formula value = F.Id("v");
        Formula designType = Call("ToroidalObserverDesign", indexType);
        Formula selectedType = Call("Finset", indexType);
        Formula windowType = Call("Set", complex);
        Formula twistValue = Call("twist", design, observer, point);
        Formula visibleRegion = Seq(
            OpenBrace, point, Sp, InMacro, Sp, complex, Sp, Mid, Sp,
            twistValue, Sp, Neq, Sp, D(0), CloseBrace);
        Formula selectedUnion = Call(
            "Union", Seq(observer, Sp, InMacro, Sp, selected), visibleRegion);
        Formula selectedCost = Seq(
            Sum, Underscore, Grp(observer, Sp, InMacro, Sp, selected), Sp,
            Call("cost", design, observer));
        Formula candidates = Seq(
            OpenBrace, value, Sp, InMacro, Sp, extendedReal, Sp, Mid, Sp,
            Exists, Sp, Typed(selected, selectedType), Comma, Sp,
            window, Sp, Subseteq, Sp, selectedUnion, Sp, Land, Sp,
            value, Sp, Eq, Sp, selectedCost, CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(indexType, type), Comma, Sp,
                Typed(design, designType), Comma, Sp,
                Typed(window, windowType), Comma),
            Seq(
                Call("toroidalObserverCost", design, window), Sp, Eq, Sp,
                Call("sInf", candidates), Dot),
        ]));
    }
}

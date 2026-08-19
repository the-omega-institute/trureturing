using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class CompletionIsomorphismCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completion map is an equivalence exactly under separation and unique realization.",
        H("Completion Isomorphism Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-map-equivalence-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion."
                        + "completion_map_equiv_iff"),
                H("Completion is equivalent to separation and unique realization"),
                StatementSource.FromAuthor(CompletionCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a type-valued inverse-stage system with restriction channels "
                            + "satisfying identity and composition. A compatible family has one "
                            + "coordinate at every stage and is preserved by every restriction.")),
                    Paragraph(Text(
                        "A compatible family of probes q induces the canonical map from X to "
                            + "compatible stage families. That map underlies an equivalence "
                            + "exactly when the probes jointly separate points and every compatible "
                            + "family is realized by a unique point of X.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplied the exact Equiv.ofBijective constructor, which "
                            + "the backward proof applies after proving injectivity from joint "
                            + "separation and surjectivity from realization. Repository search "
                            + "found a related kernel-quotient theorem and finite itinerary "
                            + "instances, but no theorem with both clauses for the candidate X.")),
                    Paragraph(Text(
                        "This statement is explicitly at the level of types. In a category with "
                            + "additional structure, an underlying bijection needs separate "
                            + "structure-preservation evidence. Also, surjectivity alone supplies "
                            + "existence rather than uniqueness; uniqueness here follows from the "
                            + "equivalence, or from realization together with joint separation."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

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

    private static Formula CompletionCriterionFormula()
    {
        Formula indexType = F.Id("I");
        Formula source = F.Id("X");
        Formula system = F.Id("S");
        Formula projection = F.Id("q");
        Formula index = F.Id("i");
        Formula point = F.Id("x");
        Formula other = F.Id("y");
        Formula family = F.Id("a");
        Formula equivalence = F.Id("e");
        Formula families = Call("CompatibleFamilies", system);
        Formula map = Call("completionMap", system, projection);
        Formula projectionAt = Seq(projection, Underscore, Grp(index));
        Formula pointCoordinate = Apply(projectionAt, point);
        Formula otherCoordinate = Apply(projectionAt, other);
        Formula familyCoordinate = Seq(family, Underscore, Grp(index));

        Formula equivalenceClause = Seq(
            Exists, Sp, equivalence, Colon, Sp, source, Sp, Equiv, Sp, families,
            Comma, Sp, Call("toFun", equivalence), Sp, Eq, Sp, map);

        Formula separationClause = Seq(
            Forall, Sp, point, Comma, Sp, other, Colon, Sp, source, Comma, Sp,
            Open, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            pointCoordinate, Sp, Eq, Sp, otherCoordinate, Close,
            Sp, Rightarrow, Sp, point, Sp, Eq, Sp, other);

        Formula realizationClause = Seq(
            Forall, Sp, family, Colon, Sp, families, Comma, Sp,
            Exists, Bang, Sp, point, Colon, Sp, source, Comma, Sp,
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            pointCoordinate, Sp, Eq, Sp, familyCoordinate);

        return Disp(Seq(
            Forall, Sp, indexType, Comma, Sp, source, Comma, Sp,
            system, Colon, Sp, Call("InverseStageSystem", indexType), Comma, Sp,
            projection, Comma, Sp,
            Call("CompatibleProjection", system, projection),
            Sp, Rightarrow, Sp, Nl,
            Open,
            Open, equivalenceClause, Close, Sp, Iff, Sp, Nl,
            Open,
            Open, separationClause, Close, Sp, Land, Sp, Nl,
            Open, realizationClause, Close,
            Close,
            Close, Dot));
    }
}

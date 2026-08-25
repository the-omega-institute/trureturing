using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class FixedPointMultiplicityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interpretation/FixedPointMultiplicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powerset endomorphisms realize every fixed-point multiplicity, while a unique "
            + "fixed point need not belong to a nonempty actuality predicate.",
        H("Fixed-Point Multiplicity and Actuality"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-point-multiplicity-and-actuality-gap"),
            DeclarationHandle.Create(
                DeclarationPrefix + "fixed_point_multiplicity_and_actuality_gap"),
            H("Self-consistency neither forces uniqueness nor selects actuality"),
            StatementSource.FromAuthor(MultiplicityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Complement on subsets of a singleton has no fixed point; a constant-empty "
                        + "map has exactly one; intersection with the Boolean singleton has "
                        + "distinct fixed points; and union with the empty set fixes every "
                        + "subset of the singleton.")),
                Paragraph(Text(
                    "The same multiple-fixed-point construction directly refutes uniqueness. "
                        + "For actuality, the theorem supplies a nonempty predicate on singleton "
                        + "subsets that excludes every fixed point of the uniquely fixing "
                        + "constant-empty map. The source's selector list is qualitative guidance "
                        + "without in-scope predicates, so no selector semantics are invented."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
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

    private static Formula MembershipBinder(Formula state, Formula carrier) =>
        Seq(state, Colon, Sp, Apply("Set", carrier));

    private static Formula IntersectionFixed(Formula state) =>
        Seq(Apply("inter", state, Seq(OpenBrace, F.Id("false"), CloseBrace)),
            Sp, Eq, Sp, state);

    private static Formula MultiplicityFormula()
    {
        Formula singletonCarrier = F.Id("Unit");
        Formula booleanCarrier = F.Id("Bool");
        Formula state = F.Id("S");
        Formula other = F.Id("T");
        Formula actual = Seq(Mathcal, Grp(F.Id("A")));
        Formula emptyFixed = Seq(Emptyset, Sp, Eq, Sp, state);

        Formula noFixedPoint = Seq(
            Open,
            Neg, Exists, Sp, MembershipBinder(state, singletonCarrier), Comma, Sp,
            Apply("compl", state), Sp, Eq, Sp, state,
            Close);
        Formula oneFixedPoint = Seq(
            Open,
            Exists, Bang, Sp, MembershipBinder(state, singletonCarrier), Comma, Sp,
            emptyFixed,
            Close);
        Formula multipleFixedPoints = Seq(
            Open,
            Exists, Sp, MembershipBinder(state, booleanCarrier), Comma, Sp,
            MembershipBinder(other, booleanCarrier), Comma, Sp,
            state, Sp, Neq, Sp, other, Sp, Land, Sp,
            IntersectionFixed(state), Sp, Land, Sp, IntersectionFixed(other),
            Close);
        Formula allFixed = Seq(
            Open,
            Forall, Sp, MembershipBinder(state, singletonCarrier), Comma, Sp,
            Apply("union", state, Emptyset), Sp, Eq, Sp, state,
            Close);
        Formula nonunique = Seq(
            Open,
            Open, Exists, Sp, MembershipBinder(state, booleanCarrier), Comma, Sp,
            IntersectionFixed(state), Close,
            Sp, Land, Sp,
            Open, Neg, Exists, Bang, Sp,
            MembershipBinder(state, booleanCarrier), Comma, Sp,
            IntersectionFixed(state), Close,
            Close);
        Formula notActual = Seq(
            Open,
            Exists, Sp, actual, Colon, Sp,
            Apply("Set", Apply("Set", singletonCarrier)), Comma, Sp,
            Apply("Nonempty", actual), Sp, Land, Sp,
            Open, Exists, Bang, Sp, MembershipBinder(state, singletonCarrier), Comma, Sp,
            emptyFixed, Close, Sp, Land, Sp,
            Forall, Sp, MembershipBinder(state, singletonCarrier), Comma, Sp,
            emptyFixed, Sp, Rightarrow, Sp, Neg, Sp,
            state, Sp, InMacro, Sp, actual,
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            noFixedPoint, Sp, Land, RowBreak, Grp(),
            oneFixedPoint, Sp, Land, RowBreak, Grp(),
            multipleFixedPoints, Sp, Land, RowBreak, Grp(),
            allFixed, Sp, Land, RowBreak, Grp(),
            nonunique, Sp, Land, RowBreak, Grp(),
            notActual, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

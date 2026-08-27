using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class ClosedConvexDistanceWitnessDualityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/MetricGeometryLaws/ClosedConvexDistanceWitnessDuality."
            + "closed_convex_distance_witness_duality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distance to a compact convex behavior image equals its optimal witness violation.",
        H("Closed Convex Distance-Witness Duality"),
        Blocks(Describe.Lean(
            DescribeId.Create("closed-convex-distance-witness-duality"),
            DeclarationHandle.Create(Declaration),
            H("Distance equals the supremum of normalized support-witness violations"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let E be a real normed vector space and I a nonempty compact convex subset. "
                        + "Compactness is the inherited behavior-image condition and makes every "
                        + "real support value finite.")),
                Paragraph(Text(
                    "For a continuous real linear witness c, the support value is the supremum "
                        + "of c on I. The public supremum ranges over the complete dual unit ball.")),
                Paragraph(Text(
                    "The upper bound follows from the operator norm inequality. The reverse bound "
                        + "normalizes a Hahn-Banach separator between I and each ball whose radius "
                        + "is strictly below the distance."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = F.Id("E");
        Formula image = F.Id("I");
        Formula signature = F.Id("y");
        Formula witness = F.Id("c");
        Formula realized = F.Id("z");
        Formula strongDual = Call("StrongDual", reals, space);
        Formula support = Seq(
            Operatorname, Grp(F.Id("sup")), Underscore,
            Grp(realized, InMacro, Sp, image), Sp,
            Apply(witness, realized));
        Formula violation = Seq(
            Apply(witness, signature), Sp, Minus, Sp, support);
        Formula witnessSupremum = Seq(
            Operatorname, Grp(F.Id("sup")), Underscore,
            Grp(
                witness, Colon, Sp, strongDual, Comma, Sp,
                new Formula.Norm(witness), Sp, Leq, Sp, D(1)),
            Sp, Grp(violation));
        Formula assumptions = And(
            Call("NormedAddCommGroup", space),
            And(
                Call("NormedSpace", reals, space),
                And(
                    Call("IsCompact", image),
                    And(Call("Convex", reals, image), Call("Nonempty", image)))));
        Formula conclusion = EqualFormula(
            Call("infDist", signature, image), witnessSupremum);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("E", type),
                Bound("I", Call("Set", space)),
                Bound("y", space),
            ],
            Implies(assumptions, conclusion)));
    }
}

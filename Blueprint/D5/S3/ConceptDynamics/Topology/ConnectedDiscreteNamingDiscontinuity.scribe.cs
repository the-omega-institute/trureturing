using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class ConnectedDiscreteNamingDiscontinuityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Topology/ConnectedDiscreteNamingDiscontinuity."
            + "connected_discrete_naming_discontinuity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected space has no nonconstant continuous discrete naming map.",
        H("Connected Discrete Naming Discontinuity"),
        Blocks(Describe.Lean(
            DescribeId.Create("connected-discrete-naming-discontinuity"),
            DeclarationHandle.Create(Declaration),
            H("Nonconstant discrete naming forces discontinuity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let X be connected and N carry the discrete topology. Every continuous "
                        + "map from X to N has equal values at every pair of points.")),
                Paragraph(Text(
                    "The second public clause is the direct contrapositive: a pair of points "
                        + "with distinct names rules out continuity of the same naming map.")),
                Paragraph(Text(
                    "The proof applies the frozen connected-to-discrete rigidity owner and "
                        + "uses the resulting equality against the witnessed distinct values."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula sourceType = F.Id("X");
        Formula nameType = F.Id("N");
        Formula name = F.Id("nu");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula continuous = Call("Continuous", name);
        Formula valuesEqual = Seq(
            Apply(name, first), Sp, Eq, Sp, Apply(name, second));
        Formula valuesDiffer = Seq(
            Apply(name, first), Sp, Neq, Sp, Apply(name, second));
        Formula constantClause = Seq(
            continuous, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, sourceType, Comma, Sp,
            valuesEqual);
        Formula discontinuityClause = Seq(
            Open,
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, sourceType, Comma, Sp,
            valuesDiffer,
            Close, Sp, Rightarrow, Sp, Neg, continuous);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, sourceType, Comma, Sp, nameType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Typeclass("TopologicalSpace", sourceType), Comma, Sp,
            Typeclass("ConnectedSpace", sourceType), Comma,
            RowBreak, Grp(),
            Typeclass("TopologicalSpace", nameType), Comma, Sp,
            Typeclass("DiscreteTopology", nameType), Comma,
            RowBreak, Grp(),
            name, Colon, Sp, sourceType, Sp, To, Sp, nameType, Comma,
            RowBreak, Grp(),
            Open, constantClause, Close, Sp, Land,
            RowBreak, Grp(),
            Open, discontinuityClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);
}

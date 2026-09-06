using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class FourRoleIndependenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Fibers/FourRoleIndependence."
            + "four_role_independence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four explicit Boolean models separate cut, flow, admissibility, and anchor.",
        H("Four-Role Independence"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-role-independence"),
            DeclarationHandle.Create(Declaration),
            H("Each observer role varies independently"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each row shares three coordinates and changes only the fourth. "
                        + "Identity versus a constant cut witnesses CUT independence, and "
                        + "identity versus Boolean negation witnesses FLOW independence.")),
                Paragraph(Text(
                    "Universal admissibility versus equality to false separates ADMIT while "
                        + "both predicates accept the false anchor. Universal admissibility "
                        + "then permits false and true as distinct accepted anchors."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ExistsMany(
        IEnumerable<Formula.BoundVariable> variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula proposition = F.Id("Prop");
        Formula boolMap = Arrow(boolean, boolean);
        Formula predicate = Arrow(boolean, proposition);

        Formula cutFirst = F.Id("q1");
        Formula cutSecond = F.Id("q2");
        Formula cut = F.Id("q");
        Formula flowFirst = F.Id("F1");
        Formula flowSecond = F.Id("F2");
        Formula flow = F.Id("F");
        Formula admitFirst = F.Id("A1");
        Formula admitSecond = F.Id("A2");
        Formula admit = F.Id("A");
        Formula anchorFirst = F.Id("a1");
        Formula anchorSecond = F.Id("a2");
        Formula anchor = F.Id("a");

        Formula cutRow = ExistsMany(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("q1"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("q2"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("F"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), predicate),
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), boolean),
            ],
            And(NotEqual(cutFirst, cutSecond), Apply(admit, anchor)));

        Formula flowRow = ExistsMany(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("F1"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("F2"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), predicate),
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), boolean),
            ],
            And(NotEqual(flowFirst, flowSecond), Apply(admit, anchor)));

        Formula admitRow = ExistsMany(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("F"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("A1"), predicate),
                new Formula.BoundVariable(FormulaIdentifier.Create("A2"), predicate),
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), boolean),
            ],
            And(
                NotEqual(admitFirst, admitSecond),
                And(Apply(admitFirst, anchor), Apply(admitSecond, anchor))));

        Formula anchorRow = ExistsMany(
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("F"), boolMap),
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), predicate),
                new Formula.BoundVariable(FormulaIdentifier.Create("a1"), boolean),
                new Formula.BoundVariable(FormulaIdentifier.Create("a2"), boolean),
            ],
            And(
                NotEqual(anchorFirst, anchorSecond),
                And(Apply(admit, anchorFirst), Apply(admit, anchorSecond))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, cutRow, Close, Sp, Land, RowBreak, Grp(),
            Open, flowRow, Close, Sp, Land, RowBreak, Grp(),
            Open, admitRow, Close, Sp, Land, RowBreak, Grp(),
            Open, anchorRow, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

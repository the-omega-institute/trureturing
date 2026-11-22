using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RootPrimitiveFourierDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local separation of the actual root modes",
        H("Separation from a fixed frequency"),
        Blocks(Describe.Lean(DescribeId.Create("actual-frequency-gap"),
            DeclarationHandle.Create(Owner + ".actual_frequency_gap"),
            H("Positive gap outside the matching frequency"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write v(r,k)=(ρₖ−1/2)/r, where ρₖ runs over actual nontrivial zeta "
                    + "zero occurrences with analytic multiplicity.")),
                Paragraph(Text("A mode within distance 1 of w comes from a zero in the closed disk "
                    + "of radius r(1+‖w‖) about 1/2. The distinct zeros in that disk form a finite set. "
                    + "Remove w from its rescaled image and take a ball centered at w in the open "
                    + "complement. Cap the radius of that ball at 1 to include all remaining modes "
                    + "in the estimate."))),
            DescribeRole.Theorem))));

    private static Formula Domain(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Statement()
    {
        var r = Id("r");
        var w = Id("w");
        var d = Id("d");
        var mode = Call("v", r, Id("k"));
        var lowerBound = Le(d, new Formula.Norm(Subtract(mode, w)));
        return F.Disp(All("r", Domain("R"), Imp(Lt(Num(0), r), All("w", Domain("C"),
            Exists("d", Domain("R"), And(Lt(Num(0), d),
                All("k", Domain("N"), Imp(NotEqual(mode, w), lowerBound))))))));
    }
}

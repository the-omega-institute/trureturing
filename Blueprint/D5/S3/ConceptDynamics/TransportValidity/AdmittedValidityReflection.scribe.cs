using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TransportValidity;

internal sealed class AdmittedValidityReflectionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TransportValidity/AdmittedValidityReflection."
            + "validity_reflected_by_admitted_surjection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjectivity on admitted states reflects validity of pulled-back predicates.",
        H("Admitted Validity Reflection"),
        Blocks(Describe.Lean(
            DescribeId.Create("validity-reflected-by-admitted-surjection"),
            DeclarationHandle.Create(Declaration),
            H("Admitted surjectivity reflects validity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Every admitted target state has an admitted source preimage. Pullback validity "
                    + "at that preimage transports along its displayed projection equality to "
                    + "validity of the target predicate."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = F.Id("Prop");
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula sourceAdmission = F.Id("AdmX");
        Formula targetAdmission = F.Id("AdmY");
        Formula transport = F.Id("h");
        Formula predicate = F.Id("P");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula preimage = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("x"),
            source,
            And(
                Apply(sourceAdmission, x),
                Equal(Apply(transport, x), y)));
        Formula admittedSurjective = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("y"),
            target,
            Implies(Apply(targetAdmission, y), preimage));
        Formula sourceValid = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            source,
            Implies(
                Apply(sourceAdmission, x),
                Apply(predicate, Apply(transport, x))));
        Formula targetValid = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("y"),
            target,
            Implies(Apply(targetAdmission, y), Apply(predicate, y)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("Y", type),
                Bound("AdmX", Arrow(source, proposition)),
                Bound("AdmY", Arrow(target, proposition)),
                Bound("h", Arrow(source, target)),
                Bound("P", Arrow(target, proposition)),
            ],
            Implies(And(admittedSurjective, sourceValid), targetValid)));
    }
}

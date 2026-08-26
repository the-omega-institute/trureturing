using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TransportValidity;

internal sealed class OldLanguageValidityConservativityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity."
            + "old_language_validity_conservative";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A projection that preserves admission and covers every admitted old state preserves "
            + "and reflects validity of every old predicate.",
        H("Old-Language Validity Conservativity"),
        Blocks(Describe.Lean(
            DescribeId.Create("old-language-validity-is-conservative"),
            DeclarationHandle.Create(Declaration),
            H("Old-language validity is conservative"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first displayed premise expands admission preservation pointwise: an "
                        + "admitted extension state projects to an admitted old state. The second "
                        + "expands admitted-domain surjectivity: every admitted old state has an "
                        + "admitted extension preimage.")),
                Paragraph(Text(
                    "Preservation pulls old validity back along the projection. Reflection chooses "
                        + "an admitted preimage of each old state, so validity of the pullback "
                        + "returns validity of the original predicate."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = F.Id("Prop");
        Formula oldState = F.Id("X");
        Formula extensionState = F.Id("XPrime");
        Formula oldAdmission = F.Id("Adm");
        Formula extensionAdmission = F.Id("AdmPrime");
        Formula projection = F.Id("p");
        Formula predicate = F.Id("P");
        Formula x = F.Id("x");
        Formula xPrime = F.Id("xPrime");

        Formula admissionPreserving = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("xPrime"),
            extensionState,
            Implies(
                Call("AdmPrime", xPrime),
                Call("Adm", Call("p", xPrime))));
        Formula preimage = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("xPrime"),
            extensionState,
            And(
                Call("AdmPrime", xPrime),
                Equal(Call("p", xPrime), x)));
        Formula admissionSurjective = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            oldState,
            Implies(Call("Adm", x), preimage));
        Formula oldValidity = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            oldState,
            Implies(Call("Adm", x), Call("P", x)));
        Formula extensionValidity = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("xPrime"),
            extensionState,
            Implies(
                Call("AdmPrime", xPrime),
                Call("P", Call("p", xPrime))));
        Formula conclusion = new Formula.Logic(
            oldValidity,
            FormulaLogicOperator.Iff,
            extensionValidity);
        Formula hypotheses = And(admissionPreserving, admissionSurjective);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new(FormulaIdentifier.Create("X"), type),
                new(FormulaIdentifier.Create("XPrime"), type),
                new(FormulaIdentifier.Create("Adm"), Arrow(oldState, proposition)),
                new(FormulaIdentifier.Create("AdmPrime"), Arrow(extensionState, proposition)),
                new(FormulaIdentifier.Create("p"), Arrow(extensionState, oldState)),
                new(FormulaIdentifier.Create("P"), Arrow(oldState, proposition)),
            ],
            Implies(hypotheses, conclusion)));
    }
}

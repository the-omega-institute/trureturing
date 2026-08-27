using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class DynamicProfileCausalClosureDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/DynamicProfileCausalClosure."
            + "dynamic_profile_causal_closure";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every intervention descends to the complete control profile through the "
            + "canonical right shift of action indices.",
        H("Dynamic Profile Causal Closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("dynamic-profile-carries-every-intervention-by-right-shift"),
            DeclarationHandle.Create(Declaration),
            H("The dynamic profile carries every intervention by right shift"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The complete profile is constructed from the public readout and the "
                        + "monoid action: its coordinate at an action records the readout after "
                        + "that action is applied to the state.")),
                Paragraph(Text(
                    "After a new intervention, evaluating the resulting profile at a continuation "
                        + "is therefore the old profile at the continuation multiplied on the "
                        + "right by that intervention. The displayed commuting equation exposes "
                        + "this macroscopic update directly."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula monoid = F.Id("M");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula action = F.Id("u");
        Formula point = F.Id("x");
        Formula profile = F.Id("phi");
        Formula continuation = F.Id("m");
        Formula type = F.Seq(F.Operatorname, F.Grp(F.Id("Type")));
        Formula actionMap = OpenLambda(
            point,
            new Formula.Binary(action, FormulaBinaryOperator.Multiply, point));
        Formula shiftedProfile = OpenLambda(
            profile,
            OpenLambda(
                continuation,
                Apply(
                    profile,
                    new Formula.Binary(
                        continuation,
                        FormulaBinaryOperator.Multiply,
                        action))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("M", type),
                Bound("X", type),
                Bound("O", type),
            ],
            new Formula.Logic(
                new Formula.Logic(
                    Call("Monoid", monoid),
                    FormulaLogicOperator.And,
                    Call("MulAction", monoid, state)),
                FormulaLogicOperator.Implies,
                new Formula.BindMany(
                    FormulaQuantifier.ForAll,
                    [
                        Bound("q", new Formula.TypeArrow(state, output)),
                        Bound("u", monoid),
                    ],
                    Equal(
                        Compose(Call("controlProfile", readout), actionMap),
                        Compose(shiftedProfile, Call("controlProfile", readout)))))));
    }

    private static Formula Compose(Formula left, Formula right) =>
        F.Seq(left, F.Sp, F.Circ, F.Sp, right);

    private static Formula OpenLambda(Formula variable, Formula value) =>
        F.Seq(F.Open, variable, F.Sp, F.Mapsto, F.Sp, value, F.Close);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(F.Seq(F.Operatorname, F.Grp(F.Id(name))), arguments);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}

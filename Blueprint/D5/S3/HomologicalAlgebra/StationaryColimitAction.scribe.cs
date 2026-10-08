using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class StationaryColimitActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/StationaryColimitAction.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => And(Implies(a, b), Implies(b, a));
    private static Formula Id(string name) => F.Id(name);
    private static Formula End => Call("ModuleEnd", Id("R"), Id("M"));
    private static Formula IdentityFamily => All(
        Equal(Call("induced", Id("T"), Call("apply", Id("P"), Id("g")), Call("apply", Id("commutes"), Id("g"))),
            Call("linearIdentity", Call("StationaryModule", Id("T")))), B("g", Id("Gamma")));
    private static Formula CommonStage => Exists("N", Id("Nat"), All(
        Equal(Call("compose", Call("power", Id("T"), Id("N")), Call("apply", Id("P"), Id("g"))),
            Call("power", Id("T"), Id("N"))), B("g", Id("Gamma"))));
    private static Formula Claim => All(Iff(IdentityFamily, CommonStage),
        B("R", Id("Type")), B("commRingR", Call("CommRing", Id("R"))),
        B("M", Id("Type")), B("addGroupM", Call("AddCommGroup", Id("M"))),
        B("moduleM", Call("Module", Id("R"), Id("M"))),
        B("I", Id("Type")), B("finiteI", Call("Fintype", Id("I"))),
        B("Gamma", Id("Type")), B("finiteGamma", Call("Fintype", Id("Gamma"))),
        B("basis", Call("Basis", Id("I"), Id("R"), Id("M"))),
        B("T", End), B("P", Call("Function", Id("Gamma"), End)),
        B("commutes", All(Call("Commute", Call("apply", Id("P"), Id("g")), Id("T")), B("g", Id("Gamma")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite commuting family is detected at a single stage of a finite-rank stationary module colimit.",
        H("Finite-stage detection of a stationary action"), Blocks(
            Describe.Lean(DescribeId.Create("finite-family-stationary-identity"),
                DeclarationHandle.Create(Prefix + "finite_family_inert_iff_eventual"), H("One common annihilation stage"),
                StatementSource.FromAuthor(Disp(Claim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("StationaryModule(T) is the actual module direct limit with transition from stage i to stage j equal to T raised to j minus i. The commuting endomorphism P(g) induces the displayed map on this direct limit. Powers of endomorphisms use composition, so the finite-stage equation is T^N composed with P(g) equals T^N.")),
                    Paragraph(Text("Equality of two stage-zero classes is witnessed at a later stage by direct-limit exactness. There are finitely many basis vectors and finitely many family members; taking finite maxima gives one N for all of them. Conversely the same finite-stage equation holds after every starting stage, so it forces identity on the entire colimit. The exponent N may be zero, the basis may be empty, and the family need not be a group action."))), DescribeRole.Theorem))));
}

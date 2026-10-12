using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardBeamColimitCutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer cuts in the original stationary row colimit.",
        H("Integer cuts in the original stationary row colimit"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("integer-cut-native-stage"),
                DeclarationHandle.Create(Prefix + "intStage"),
                H("Integer cuts in the original natural-stage colimit"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Apply(Call("intStage", I("T"), I("n")), I("z")),
                                Apply(
                                    Call("stage", I("T"), Call("toNat", I("n"))),
                                    Apply(Call("power", I("T"), Call("toNat", Call("negate", I("n")))), I("z")))),
                            B("n", I("Int")),
                            B("z", I("M"))),
                        B("M", I("Type")),
                        B("addM", Call("AddCommGroup", I("M"))),
                        B("moduleM", Call("IntModule", I("M"))),
                        B("T", Call("IntEnd", I("M")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("M is any AddCommGroup with Module Int M, T : Module.End Int M. stage T N is the original Module.DirectLimit.of at N:Nat with stationaryTransition T i j hij = T^(j-i). intStage T n is stage T n.toNat composed with T^((-n).toNat). For n>=0 it is the original stage; for n<0 it advances to stage zero using the nonnegative power -n. No inverse matrix, transition injectivity or torsion-free premise is used."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("every-upper-stage-independence"),
                DeclarationHandle.Create(Prefix + "intStage_at"),
                H("Every nonnegative upper stage gives the same class"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Apply(Call("intStage", I("T"), I("n")), I("z")),
                                Apply(
                                    Call("stage", I("T"), I("N")),
                                    Apply(
                                        Call(
                                            "power",
                                            I("T"),
                                            Call("toNat", Call("integerDifference", I("N"), I("n")))),
                                        I("z")))),
                            B("n", I("Int")),
                            B("N", I("Nat")),
                            B("hn", Le(I("n"), Call("intCast", I("N")))),
                            B("z", I("M"))),
                        B("M", I("Type")),
                        B("addM", Call("AddCommGroup", I("M"))),
                        B("moduleM", Call("IntModule", I("M"))),
                        B("T", Call("IntEnd", I("M")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("intCast is the natural-to-integer coercion, integerDifference(N,n) is (N:Int)-n, and the exponent is its toNat. This is the exact n<=(N:Int) hypothesis. The existing direct-limit stage relation proves the equality. intStage_refine then states intStage T n z = intStage T (n+r) (T^r z) for every r:Nat. All powers advance rather than invert T."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("true-unit-shift-cut-direction"),
                DeclarationHandle.Create(Prefix + "intStage_shift"),
                H("Moving the cut down by one induces the stationary transition"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Apply(Call("intStage", I("T"), Call("previousCut", I("n"))), I("z")),
                                Apply(Call("Theta", I("T")), Apply(Call("intStage", I("T"), I("n")), I("z")))),
                            B("n", I("Int")),
                            B("z", I("M"))),
                        B("M", I("Type")),
                        B("addM", Call("AddCommGroup", I("M"))),
                        B("moduleM", Call("IntModule", I("M"))),
                        B("T", Call("IntEnd", I("M")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("previousCut(n)=n-1. Theta T is induced T T (Commute.refl T) on StationaryModule T, with Theta(stage N z)=stage N (T z). Refining from n-1 to n proves this direction, including n=0 and cut -1. It is the direction required by the actual left shift x_t -> x_(t+1)."))),
                DescribeRole.Theorem))));
}

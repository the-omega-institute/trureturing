using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetNativeOddObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The surviving native integer odd class.",
        H("The surviving native integer odd class"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in the corresponding definitions; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("explicit-integral-odd-alternating-row"),
                DeclarationHandle.Create(Prefix + "resetOddVector"),
                H("An explicit row with both integer sign coefficients"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Apply(Call("resetOddVector", I("q")), I("j")),
                            Call(
                                "integerScale",
                                Call("power", new Formula.Negate(Num(1)), Call("finValue", I("j"))),
                                Call("antiUnit"))),
                        B("q", I("Nat")),
                        B("j", Call("Fin", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("resetOddVector q belongs to VertexModule Sign q, with Sign=Multiplicative Bool and tau=ofAdd true. antiUnit means single (1:Sign) (1:Int) - single tau (1:Int) in MonoidAlgebra Int Sign. integerScale is the Int module action and finValue(j)=j.val. Thus w_i=(-1)^i(1-tau) retains both coefficients. No positivity or odd premise is needed to define the row."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("true-original-native-stationary-transition"),
                DeclarationHandle.Create(Prefix + "resetTheta"),
                H("Theta is induced by the original row transition"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call(
                            "hasType",
                            Call("resetTheta", I("q")),
                            Call("IntEnd", Call("DimensionGroup", Call("resetMatrix", I("q"))))),
                        B("q", I("Nat"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("resetTheta q=induced (transition(resetMatrix q)) (transition(resetMatrix q)) (Commute.refl _), on the existing DimensionGroup(resetMatrix q). hasType displays the definition's type. The integerMatrix casts the original natural group matrix into Int[C2], and transition is the original row toLinearMapRight'. The reset label multiplies each input coordinate on the RIGHT. groupAction(resetMatrix q) tau is the separate complement action; it is not the definition of Theta."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("all-odd-iterates-nonzero-integer-coefficient"),
                DeclarationHandle.Create(Prefix + "reset_odd_transition_pow_coeff_one"),
                H("A nonzero coefficient survives every transition iterate"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Call(
                                "identityCoefficientAtZero",
                                Apply(
                                    Call("power", Call("transition", Call("resetMatrix", I("q"))), I("k")),
                                    Call("resetOddVector", I("q"))),
                                I("hq")),
                            Call("power", new Formula.Negate(Num(1)), I("k"))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q"))),
                        B("ho", Call("Odd", I("q"))),
                        B("k", I("Nat"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("identityCoefficientAtZero(v,hq) is (v (0 : Fin q)).coeff (1:Sign), using hq to construct the zero suffix. reset_odd_transition computes T w=-w: the odd alternating sum equals one, multiplication of 1-tau by tau gives its negative, and every successor coordinate reads its predecessor. reset_odd_transition_pow then gives T^k w=(-1)^k w for every natural k. Its displayed suffix-zero identity coefficient is the nonzero integer unit (-1)^k. The pairwise alternating-sum induction begins at q=1; no mixing or q>=3 hypothesis is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-colimit-nonzero-killed-class"),
                DeclarationHandle.Create(Prefix + "reset_odd_killed_class"),
                H("A genuinely surviving original integer class is killed by id plus Theta"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        And(
                            NotEqual(Call("resetOddClass", I("q")), Num(0)),
                            Equal(
                                Apply(
                                    Call(
                                        "endSum",
                                        Call(
                                            "linearIdentity",
                                            Call("DimensionGroup", Call("resetMatrix", I("q")))),
                                        Call("resetTheta", I("q"))),
                                    Call("resetOddClass", I("q"))),
                                Num(0))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q"))),
                        B("ho", Call("Odd", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("resetOddClass q is the ORIGINAL natural-stage colimit class at stage zero of resetOddVector q. If it were zero, Module.DirectLimit.exists_eq_of_of_eq would force a later iterate of that row to vanish, contradicting its explicit coefficient (-1)^k. The identity plus resetTheta kills the class because T w=-w. This survival argument uses neither transition injectivity nor a torsion-free premise, nor a spectral-radius or Parry scalar argument. It includes the deterministic odd case q=1."))),
                DescribeRole.Theorem))));
}

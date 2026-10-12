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
            Describe.Lean(DescribeId.Create("original-reset-sign-label"),
                DeclarationHandle.Create(Prefix + "oddTau"),
                H("The nonidentity reset sign"),
                StatementSource.FromAuthor(Disp(Equal(I("oddTau"), Call("ofAdd", I("true"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sign is Multiplicative Bool; oddTau is ofAdd true, the nonidentity sign. This is the label used by the original coordinate formulas."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-integral-reset-label"),
                DeclarationHandle.Create(Prefix + "resetLabel"),
                H("The integral reset label"),
                StatementSource.FromAuthor(Disp(Equal(I("resetLabel"), Call("single", I("oddTau"), Num(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("single is MonoidAlgebra.single in MonoidAlgebra Int Sign. resetLabel is the original right-multiplication label, with coefficient one at oddTau."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-transition-zero-coordinate"),
                DeclarationHandle.Create(Prefix + "transition_zero"),
                H("The original transition at coordinate zero"),
                StatementSource.FromAuthor(Disp(Forall(
                    Equal(Apply(Call("transition", Call("resetMatrix", Call("succ", I("N")))), I("v"), Num(0)),
                        Call("mul", Call("sumCoordinates", I("v")), I("resetLabel"))),
                    B("N", I("Nat")), B("v", Call("VertexModule", I("Sign"), Call("succ", I("N"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("succ(N)=N+1; sumCoordinates(v) is the sum over Fin(N+1), and zero is the zero Fin coordinate. The formula is T(v)(0)=(sum v)*resetLabel in the original integer right-row convention. It is the coordinate fact used by both the odd obstruction and the finite companion bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-transition-successor-coordinate"),
                DeclarationHandle.Create(Prefix + "transition_succ"),
                H("The original transition at successor coordinates"),
                StatementSource.FromAuthor(Disp(Forall(
                    Equal(Apply(Call("transition", Call("resetMatrix", Call("succ", I("N")))), I("v"), Call("finSucc", I("j"))),
                        Apply(I("v"), Call("castSucc", I("j")))),
                    B("N", I("Nat")), B("v", Call("VertexModule", I("Sign"), Call("succ", I("N")))),
                    B("j", Call("Fin", I("N")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For j:Fin N, finSucc(j) is j.succ and castSucc(j) is j.castSucc in Fin(N+1). Thus T(v)(j.succ)=v(j.castSucc), including the empty successor family at N=0. Both consumers directly apply this original coordinate fact."))),
                DescribeRole.Theorem),
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
            Describe.Lean(DescribeId.Create("original-odd-row-identity-coefficient"),
                DeclarationHandle.Create(Prefix + "resetOddVector_coeff_one"),
                H("The original alternating identity coefficient"),
                StatementSource.FromAuthor(Disp(Forall(Equal(
                    Call("coeff", Apply(Call("resetOddVector", I("q")), I("i")), Num(1)),
                    Call("power", new Formula.Negate(Num(1)), Call("finValue", I("i")))),
                    B("q", I("Nat")), B("i", Call("Fin", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identity coefficient of the original row w_i is (-1)^i. "
                    + "It gives both the surviving iterate coefficient and the native character pairing."))),
                DescribeRole.Theorem),
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
            Describe.Lean(DescribeId.Create("original-native-transition-stage-identity"),
                DeclarationHandle.Create(Prefix + "resetTheta_apply_of"),
                H("Theta acts on each original stage by its row transition"),
                StatementSource.FromAuthor(Disp(Forall(
                    Equal(
                        Apply(Call("resetTheta", I("q")), Call("nativeStage", I("q"), I("n"), I("v"))),
                        Call("nativeStage", I("q"), I("n"),
                            Apply(Call("transition", Call("resetMatrix", I("q"))), I("v")))),
                    B("q", I("Nat")), B("n", I("Nat")),
                    B("v", Call("VertexModule", I("Sign"), I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("nativeStage(q,n,v) is Module.DirectLimit.of Int Nat "
                    + "(fun _ => VertexModule Sign q) (stationaryTransition (transition (resetMatrix q))) n v. "
                    + "The identity follows from Module.DirectLimit.map_apply_of for the stationary transition. "
                    + "It holds for every natural q and n, without positivity or parity assumptions. "
                    + "The native stage-zero identification uses this identity in resetNativeEquiv_theta to intertwine Theta with the original right-row transition."))),
                DescribeRole.Theorem),
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

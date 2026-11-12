using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class JointFramePureCompactnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/JointFramePureCompactness.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, F.Lt, Sp, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula CDual => C("ContinuousLinearMap", R, Space, R);
    private static Formula Three => C("Fin", D(3));
    private static Formula States => Seq(Three, To, Sp, Space);
    private static Formula Effects => Seq(Three, To, Sp, CDual);
    private static Formula K => C("base", Cone, Unit);
    private static Formula P => C("pure", Cone, Unit);
    private static Formula Exclusion(Formula p) => C("exclusion", Cone, Unit, p);
    private static Formula Joint(Formula s, Formula e) => C("jointFrame", Cone, Unit, s, e);
    private static Formula Completion => C("pureJointCompletion", Cone, Unit);
    private static Formula Incidence => C("pointBallIncidence", Cone, Unit);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));
    private static Formula Strict => All("x", Space, Imp(In(V("x"), Cone),
        Imp(Ne(V("x"), D(0)), Lt(D(0), App(Unit, V("x"))))));
    private static Formula Result(string property) => Context(
        Imp(C("IsClosed", Cone), Imp(Strict, Imp(Eq(C("span", R, Cone), C("top")),
            Imp(Completion, Imp(Incidence, C(property, P)))))));

    public DocumentDefinition Create()
    {
        Formula s = V("s"), e = V("e"), i = V("i"), j = V("j"), p = V("p"), q = V("q");
        Formula joint = Context(All("s", States, All("e", Effects,
            Iff(Joint(s, e), And(All("i", Three, In(App(s, i), K)),
                And(All("i", Three, C("proper", Cone, Unit, C("toLinearMap", App(e, i)))),
                    And(Eq(C("sum", e), C("toContinuousLinearMap", Unit)),
                        All("i", Three, All("j", Three,
                            Eq(App(App(e, i), App(s, j)), C("Kronecker", i, j)))))))))));
        Formula completion = Context(Iff(Completion, All("p", P, Ex("s", States, Ex("e", Effects,
            And(All("i", Three, In(App(s, i), P)),
                And(Eq(App(s, D(0)), p), Joint(s, e))))))));
        Formula incidence = Context(Iff(Incidence, And(
            All("p", P, All("q", P, Imp(Ne(Exclusion(p), Exclusion(q)), C("Subsingleton", C("inter", Exclusion(p), Exclusion(q)))))),
            C("Injective", C("exclusionOnPure", Cone, Unit)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Joint original three-outcome frames and point-exclusion incidence force closed and compact original pure points.",
            H("Pure compactness from joint frames"), Blocks(
                Paragraph(Text("Let V be a finite dimensional real normed space, C the entire original cone, and u its original real-linear unit. The sets K=base(C,u), P=pure(C,u), the globally proper effects and the mixed-state exclusion sets are the existing CircuitBalancedConfirmation and FacetZeroGluing objects. The closed generating cone and strict positivity of u imply compactness of K. Strict positivity also excludes nonzero lines. No finiteness or closedness of P is assumed.")),
                Def("jointFrame", "One joint three-outcome frame", joint,
                    "The three states belong to the entire original base. Each effect is nonnegative and bounded above by u on the entire original cone; their sum equals u as a functional on V. All nine state-effect readings are Kronecker readings, with Kronecker(i,j)=1 for i=j and 0 otherwise. The notation sum(e) sums over Fin 3. Continuous linear effects exhaust real-linear effects because V is finite dimensional; no restricted menu is introduced."),
                Def("pureJointCompletion", "Complete every original pure point", completion,
                    "For each p in the entire original pure set, there exist three original pure states and three original globally proper effects forming a jointFrame, with the first state equal to p. Each p may have many completions. The theorem requires neither continuity nor uniqueness of a selected completion."),
                Def("pointBallIncidence", "Incidence of entire original exclusions", incidence,
                    "For pure p and q with different entire exclusion sets, their intersection is a subsingleton. In addition, the map p to exclusion(C,u,p) on the subtype of all original pure points is injective. exclusionOnPure denotes exactly this map. No selected faces, selected pure subset or new orthogonality relation replaces the original exclusions."),
                Item("pure_closed_of_joint_completion", "The entire pure set is closed", Result("IsClosed"),
                    "Assume closedness and generation of the original cone, strict positivity of its original unit, pureJointCompletion and pointBallIncidence. Then all extreme points of the entire original base form a closed subset of V, hence also a relatively closed subset of K.",
                    "First consider one globally proper effect a confirming x and vanishing at two distinct original states y,z. Its one-face F is nonempty, compact, convex and exposed. Every extreme point of F is an original pure point. For two such points p,q, the same effect a puts both y and z in both original exclusions. The intersection condition forces those exclusions equal; injectivity gives p=q. Krein-Milman identifies F with the closed convex hull of its extreme points, so F is a singleton and x is pure. The two excluded states need not themselves be pure.",
                    "The full proper-effect interval is compact: a finite basis chosen from the generating cone bounds every effect reading between zero and the original unit reading. The basis operator-norm estimate gives boundedness, while all cone inequalities are closed. Take the compact product of three original states and three such effects. The joint unit and all nine Kronecker equations define a closed subset T of this same product. Evaluation is continuous jointly in state and effect. Any frame in T has distinct second and third states, distinguished by its second effect, so the preceding one-face argument proves its first state pure. Conversely pureJointCompletion puts every original pure point in the first-coordinate image of T. This image is compact and hence closed; all joint relations are retained together."),
                Item("pure_compact_of_joint_completion", "The entire pure set is compact", Result("IsCompact"),
                    "Under exactly the same hypotheses, P is compact. Apply the closedness conclusion inside the compact original base K using the existing inclusion of extreme points in their ambient set. Empty bases and empty pure sets are included. The one-face argument chooses an extreme point only after establishing a nonempty compact face."),
                Paragraph(Text("These are conditional consequences of joint completion and point-exclusion incidence on the original full domain. They express the compactness inference used in Quantum Origin VII, Theorem 104.6. Deriving both predicates from the original exclusion-ball condition EB of dimension at least one and the original orthogonal-pair proper-face condition remains a further mathematical obligation; these theorems do not assert that derivation or the full EB-plus-Pair theorem. They assume no spectrality, self-duality, projectivity, unique effect selection, global least confirmation or physical implementation. No literature priority is asserted.")))));
    }

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Item(string name, string title, Formula formula, params string[] prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks([.. prose.Select(p => Paragraph(Text(p)))]), DescribeRole.Theorem);
}

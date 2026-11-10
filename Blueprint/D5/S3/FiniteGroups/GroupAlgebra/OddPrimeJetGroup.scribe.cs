using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetGroupDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full original odd-prime jet group", H("Coherent lifts of actual labels"), Blocks(
            Paragraph(Text("Let p be every odd prime, including three, F=ZMod p, and K a finite F-algebra field in an arbitrary independent universe. Suppose |K|=p^n with n at least one. For A:Fin(n-1) to K put q(x)=sum_i A_i(x^(p^(i+1))-x), R=sum_i A_i, and V=Polynomial.degreeLT K p. All linear operators and equivalences below are only F-linear. The original action is rho_x=exp(xD+q(x)D^(p-1)); its labels are the original additive group Multiplicative K.")),
            Paragraph(Text("G is the subgroup of pairs (P,phi) in GL_F(V) times Aut(Multiplicative K) satisfying P rho_x=rho_(phi(x)) P for every original label x. Its label projection has image S. The finite original-pair classification forces each label of S uniquely to have phi(x)=c sigma(x), with c a unit, sigma an F-algebra automorphism, and A_i=c^(-w_i) sigma(A_i), w_i=p^(i+1)-p+1. Thus S is the actual label stabilizer, rather than a group of independently chosen coefficient data.")),
            Claim("coherentLift_intertwines", "oddprimejetgroup-lift", "Every original operator intertwines",
                Parameters(All("g", Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")),
                    All("x", Call("Multiplicative", F.Id("K")), All("v", Call("V", F.Id("p"), F.Id("K")),
                        Eq(Call("T", F.Id("g"), Call("rho", F.Id("A"), F.Id("x"), F.Id("v"))),
                            Call("rho", F.Id("A"), Call("label", F.Id("g"), F.Id("x")), Call("T", F.Id("g"), F.Id("v")))))))),
                "Write H=shear(-R), where shear(b)=I+b topShear. The degree lift B_g has coefficient j equal to c^(-j) sigma(v_j). The lift is T_g=H^(-1) B_g H. Since B_(gh)=B_g B_h, these lifts form a genuine group homomorphism. The same fixed H appears at every composition, so its adjacent inverse cancels exactly. The normalized coefficient function is q(x)+Rx=sum_i A_i x^(p^(i+1)); its weighted transformation proves intertwining of infinitesimal operators, and the existing finite-exponential bridge proves intertwining for every original representation operator."),
            Claim("sectionHom", "oddprimejetgroup-section", "A coherent group section",
                Parameters(Call("MonoidHom", Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")),
                    Call("G", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")))),
                "The homomorphism sends g to the actual pair (coherentLift(g),g). Its multiplication proof is the exact operator equality T_(gh)=T_g composed with T_h, with the ordinary product convention of original label automorphisms."),
            Claim("project_section", "oddprimejetgroup-section-project", "The section preserves actual labels",
                Parameters(All("g", Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")),
                    Eq(Call("project", Call("section", F.Id("A"), F.Id("g"))), F.Id("g")))),
                "The projection of the constructed original pair is the given original label itself."),
            Claim("unique_factorization", "oddprimejetgroup-factor", "Unique actual factorization",
                Parameters(All("z", Call("G", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")),
                    UniqueFactor())),
                "C is the kernel of the actual label projection, embedded as original pairs (X,id). It is exactly the group of invertible operators in the full actual commutant. For each z the unique factors are s=project(z) and k=z section(s)^(-1). Multiplication uses ordinary operator composition. The action on C is actual conjugation by section(s)."),
            Claim("semidirectEquiv", "oddprimejetgroup-semidirect", "The original group is a semidirect product",
                Parameters(Call("MulEquiv", Call("G", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")),
                    Call("SemidirectProduct", Call("C", F.Id("A")), Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")), Call("conjugation", F.Id("A"))))),
                "Mathlib SemidirectProduct.lift maps (k,s) to k section(s). The unique-factorization proof makes it bijective. This splits the full original group over its entire actual label stabilizer. It does not assert that the separate scalar/Galois projection of that stabilizer splits: such a further projection can remain nonsplit."),
            Claim("full_card_factorization", "oddprimejetgroup-factor-count", "Cardinality of the actual factors",
                Parameters(Eq(Call("card", Call("G", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A"))),
                    Mul(Call("card", Call("C", F.Id("A"))),
                        Call("card", Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")))))),
                "The native multiplicative equivalence yields a bijection with the product of the complete commutant-unit kernel and the actual label image."),
            Claim("commutant_cardinality", "oddprimejetgroup-kernel-count", "The unrestricted kernel count",
                Parameters(Eq(Call("card", Call("C", F.Id("A"))),
                    Mul(Sub(Pow(F.Id("p"), F.Id("n")), D(1)), Pow(F.Id("p"),
                        Add(Mul(F.Id("n"), Sub(F.Id("p"), D(2))), Mul(F.Id("n"), F.Id("n"))))))),
                "The existing unique Toeplitz coordinates and unit criterion supply one nonzero leading scalar, p-2 arbitrary field scalars, and an entirely unrestricted T in End_F(K). The latter has F-dimension n squared. The degree coordinates reserve c_0=0 and use c_(p-1) for the leading shift scalar; no coefficient is counted twice."),
            Claim("full_cardinality", "oddprimejetgroup-full-count", "The full group count",
                Parameters(Eq(Call("card", Call("G", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A"))),
                    Mul(Mul(Sub(Pow(F.Id("p"), F.Id("n")), D(1)), Pow(F.Id("p"),
                        Add(Mul(F.Id("n"), Sub(F.Id("p"), D(2))), Mul(F.Id("n"), F.Id("n"))))),
                        Call("card", Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")))))),
                "The label-stabilizer factor multiplies the commutant-unit count. The commutant alone never supplies the full group order. The source reuses the native original-pair classification, the actual commutant theorem, and Mathlib semidirect products and finite-dimensional cardinality. No literature-priority claim is made."),
            Claim("weightedStabilizerEquiv", "oddprimejetgroup-weighted", "The native weighted stabilizer",
                Parameters(All("L", Call("Type"), Seq(WithInstance("Field", F.Id("L")), Sp,
                    WithInstance("Fintype", F.Id("L")), Sp,
                    WithInstance("Algebra", Call("ZMod", F.Id("p")), F.Id("L")), Sp,
                    All("e", Call("AlgEquiv", Call("ZMod", F.Id("p")), F.Id("K"), F.Id("L")),
                        Call("MulEquiv", Call("weightedStabilizer", F.Id("A"), F.Id("e")),
                            Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A"))))))),
                "For every actual F-algebra equivalence e from K to a small finite field L, the existing native WeightedSemilinear stabilizer of the tuple e(A) is multiplicatively equivalent to S. The map sends (c,sigma) to the original label x maps to e^(-1)(c) e^(-1)(sigma(e(x))). Evaluation at one determines c and cancellation then determines sigma, proving faithfulness. The inverse weighted coefficient criterion proves exactly the image condition. Taking L=Shrink K gives this result for every original universe of K without narrowing that universe."),
            Claim("normalized_conjugation", "oddprimejetgroup-conjugation", "The unrestricted conjugation law",
                Parameters(All("g", Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")),
                    All("a", Call("Function", Call("Fin", Sub(F.Id("p"), D(1))), F.Id("K")),
                        All("T", Call("LinearMap", Call("ZMod", F.Id("p")), F.Id("K"), F.Id("K")),
                            All("v", Call("V", F.Id("p"), F.Id("K")),
                                Eq(Call("degreeLift", F.Id("g"), Call("toeplitz", F.Id("a"), F.Id("T"), F.Id("v"))),
                                    Call("toeplitz", Call("shiftTransform", F.Id("g"), F.Id("a")),
                                        Call("transformedTop", F.Id("g"), F.Id("T")),
                                        Call("degreeLift", F.Id("g"), F.Id("v"))))))))),
                "Here shiftTransform(g,a)_r means c^r sigma(a_r), and transformedTop(g,T)=sigma composed with T composed with sigma^(-1) composed with m(c^(p-1)). The scalar acts on the input, before sigma^(-1) and T. This is proved as equality on actual polynomial operators for every F-linear T, without replacing T by a scalar. Applying the degree lift to D^(p-1)v and reading its constant coefficient supplies the required input relation."),
            Claim("shear_conjugation", "oddprimejetgroup-shear", "The fixed shear changes only the top coefficient",
                All("p", Nat(), Context(All("s", F.Id("K"),
                    All("a", Call("Function", Call("Fin", Sub(F.Id("p"), D(1))), F.Id("K")),
                        All("T", Call("LinearMap", Call("ZMod", F.Id("p")), F.Id("K"), F.Id("K")),
                            All("v", Call("V", F.Id("p"), F.Id("K")),
                                Eq(Call("shear", Seq(Minus, F.Id("s")), Call("toeplitz", F.Id("a"), F.Id("T"), F.Id("v"))),
                                    Call("toeplitz", F.Id("a"), Add(F.Id("T"),
                                        Call("fieldScalar", Mul(F.Id("s"), Call("eval", F.Id("a"), D(1))))),
                                        Call("shear", Seq(Minus, F.Id("s")), F.Id("v")))))))))),
                "Thus conjugation by H_s=shear(-s) leaves every lower shift coefficient unchanged and sends T to T+m(s a_1). The proof uses that topShear annihilates positive derivative inputs, D topShear=D^(p-1), and D squared topShear=0. It uses K-linearity only on the degree-one image of topShear, where the unrestricted top map vanishes; it never assumes that the entire commutant operator is K-linear."),
            Claim("normalized_group_structure", "oddprimejetgroup-normalized", "Every original normalized coefficient map",
                NormalizedStructure(),
                "For an arbitrary F-linear q with q(1)=0, the existing coefficient bijection supplies A with Q(A)=q. Substitution gives an action on the actual kernel, a multiplicative equivalence of the entire original pair group with its semidirect product, and both exact cardinalities. Thus the coefficient presentation imposes no restriction on the original normalized q."),
            Claim("prime_field_cardinality", "oddprimejetgroup-prime-count", "The prime-field full count",
                All("p", Nat(), Context(Imp(Eq(Call("card", F.Id("K")), F.Id("p")),
                    Eq(Call("card", Call("originalGroup", D(0))),
                        Mul(Pow(Sub(F.Id("p"), D(1)), D(2)), Pow(F.Id("p"), Sub(F.Id("p"), D(1)))))))),
                "When |K|=p, the normalized coefficient tuple is empty and q=0. The weighted stabilizer is the whole native scalar-semilinear group; the Galois group has order one and the scalar group has order p-1. Therefore the full count is (p-1) squared times p^(p-1), whereas the kernel alone has order (p-1) times p^(p-1). The scalar factor is retained even for n=1."))));

    private static DocumentBlock Claim(string name, string id, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula WithInstance(string name, params Formula[] args) => Seq(OpenBracket, Call(name, args), CloseBracket);
    private static Formula Context(Formula body) => Seq(
        WithInstance("Fact", Call("Prime", F.Id("p"))), Sp,
        WithInstance("Fact", new Formula.Relation(D(2), FormulaRelationOperator.LessThan, F.Id("p"))), Sp,
        All("K", Call("Type"), Seq(WithInstance("Field", F.Id("K")), Sp,
            WithInstance("Fintype", F.Id("K")), Sp,
            WithInstance("Algebra", Call("ZMod", F.Id("p")), F.Id("K")), Sp, body)));
    private static Formula Parameters(Formula body) => All("p", Nat(), Context(
        All("n", Nat(), Imp(And(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            Eq(Call("card", F.Id("K")), Pow(F.Id("p"), F.Id("n")))),
            All("A", Call("Function", Call("Fin", Sub(F.Id("n"), D(1))), F.Id("K")), body)))));
    private static Formula NormalizedStructure() => All("p", Nat(), Context(
        All("n", Nat(), Imp(And(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            Eq(Call("card", F.Id("K")), Pow(F.Id("p"), F.Id("n")))),
            All("q", Call("LinearMap", Call("ZMod", F.Id("p")), F.Id("K"), F.Id("K")),
                Imp(Eq(Call("eval", F.Id("q"), D(1)), D(0)), NormalizedConclusion()))))));
    private static Formula NormalizedConclusion()
    {
        var group = Call("originalGroup", F.Id("q"));
        var kernel = Call("kernel", Call("project", F.Id("q")));
        var labels = Call("labelGroup", F.Id("q"));
        var count = Mul(Sub(Pow(F.Id("p"), F.Id("n")), D(1)), Pow(F.Id("p"),
            Add(Mul(F.Id("n"), Sub(F.Id("p"), D(2))), Mul(F.Id("n"), F.Id("n")))));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("alpha"),
            Call("MonoidHom", labels, Call("MulAut", kernel)),
            And(Call("Nonempty", Call("MulEquiv", group,
                    Call("SemidirectProduct", kernel, labels, F.Id("alpha")))),
                And(Eq(Call("card", kernel), count), Eq(Call("card", group),
                    Mul(count, Call("card", labels))))));
    }
    private static Formula FactorType() => Call("product", Call("C", F.Id("A")),
        Call("S", F.Id("p"), F.Id("K"), F.Id("n"), F.Id("A")));
    private static Formula Fiber(Formula x) => Eq(Mul(Call("val", Call("fst", x)),
        Call("section", F.Id("A"), Call("snd", x))), F.Id("z"));
    private static Formula UniqueFactor() => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("x"),
        FactorType(), And(Fiber(F.Id("x")), All("y", FactorType(),
            Imp(Fiber(F.Id("y")), Eq(F.Id("y"), F.Id("x"))))));
}

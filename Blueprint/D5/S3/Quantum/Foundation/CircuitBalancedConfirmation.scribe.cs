using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class CircuitBalancedConfirmationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the original closed finite dimensional real cone with a strictly positive unit, full finite pure-mixture comparison, all-reference circuit balance and reciprocal whole-cone least confirmation are equivalent.",
        H("Circuit balance and least confirmation"),
        Blocks(
            Paragraph(Text("Let A be a finite dimensional real normed vector space, C a closed cone containing zero and closed under addition and nonnegative scaling, with real span all of A. The original linear unit u is strictly positive at every nonzero point of C. Strict positivity also excludes nonzero lines in C. The chosen compatible norm gives the usual finite dimensional topology on this same A; its numerical values enter no comparison or effect definition. All effects act on the original A. No pure-generation equality, finite pure-decomposition supplier, relation preservation, reciprocity or least confirmation is a premise. The theorem includes the zero carrier as well as every original nonzero carrier.")),
            GeometryFact("base_compact", "Compactness of the entire base", Geo(
                Imp(Call("IsClosed", Id("C")), Imp(Strict(), Call("IsCompact", Base())))),
                "Closedness and strict positivity make the entire normalized base compact, including the empty base. A positive minimum of the unit on the cone's unit-sphere section bounds the norm of normalized points."),
            GeometryFact("nonneg_on_cone", "Extend pure nonnegativity to the entire cone", Geo(
                All("f", Dual(), Imp(Call("IsCompact", Base()), Imp(Strict(),
                    Imp(All("p", Pure(), Le(D(0), Call("apply", Id("f"), Id("p")))),
                        All("x", Id("A"), Imp(Member(Id("x"), Id("C")),
                            Le(D(0), Call("apply", Id("f"), Id("x")))))))))),
                "For every original linear functional f, nonnegativity on all extreme points extends first to their closed convex hull, the entire compact base, and then by positive rescaling to every cone vector. The zero vector is handled directly."),
            GeometryFact("cone_bound", "Extend pure bounds to the full proper interval", Geo(
                All("f", Dual(), Imp(Call("IsCompact", Base()), Imp(Strict(),
                    Imp(All("p", Pure(), And(Le(D(0), Call("apply", Id("f"), Id("p"))),
                        Le(Call("apply", Id("f"), Id("p")), D(1)))),
                        Call("proper", Id("C"), Id("u"), Id("f"))))))),
                "Bounds between zero and one at every global pure point imply 0<=f<=u on the entire original cone. Apply pure nonnegativity extension to f and to u-f. No finite pure-decomposition premise is required."),
            Describe.Lean(DescribeId.Create("normalized-base"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base"),
                H("The entire normalized base"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the specified C and u, base(C,u) consists of all x in C with u(x)=1. No selected preparations replace this base."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pure-points"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure"),
                H("All pure points"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The pure set P is exactly the set of extreme points of base(C,u), with extremality over the real scalars. It is not an independently chosen list and need not be finite or consist of exposed points."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("affine-extreme-image"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.affine_extreme_image"),
                H("Affine images preserve extreme points"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For additive real module carriers E and F, a convex set S, an affine map f that is injective on S, and an extreme point x of S, the image f(x) is an extreme point of the image f '' S. This is the shared generic transport used by both the Bell-polytope supplier and the whole-pair ball consumer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proper-interval"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.proper"),
                H("The full proper interval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A real linear functional f on A is proper precisely when 0 <= f(x) <= u(x) for every x in the original C. Every such f is available in this mathematical interval."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("confirming-effects"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.confirms"),
                H("All confirming proper effects"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The predicate confirms(C,u,p,f) requires f to be proper on all of C and f(p)=1. In particular the original u confirms each pure point."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lower-envelope"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.comparison"),
                H("The original comparison lower envelope"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a pure reference p, the value T_p(x) is the real infimum of f(x) over all original proper effects f confirming p. For each x in C this set of readings is nonempty and bounded below by zero. The theorem proves that its infimum is attained by the constructed effect; it does not assume attainment."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimal-relations"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit"),
                H("Actual minimal signed relations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Given a finite subset s of P, a coefficient function c on s is a circuit when c is nonzero, its weighted sum of the original pure vectors is zero, and any nonzero signed relation w supported inside the support of c has exactly that support. The finite ambient subset may contain unused labels; the actual support is the circuit. Subtype labels are distinct original pure points. No preservation of signs is imposed on competitors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("balanced-readings"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.balanced"),
                H("Balance on every circuit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A scalar assignment v on P is balanced when, for every finite subset s and every circuit c on s, the sum of c(i)v(i) is zero. Applied at reference p, the assignment is v(q)=T_q(p); reciprocity is absent from this definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-finite-mixture"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.fullMixture"),
                H("Every finite pure mixture"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Full S requires, for every pure reference p, every natural n, every list q indexed by Fin n of original pure points and every nonnegative real weight list summing to one, T_p(sum_i w_i q_i)=sum_i w_i T_{q_i}(p). Zero weights, unequal positive weights and repeated labels remain included. An empty normalized weight list is impossible, rather than excluded by a supplier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reciprocal-least-effects"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.reciprocalLeast"),
                H("Reciprocal least confirming effects"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There is a family of real linear effects e_p on A, one for each original pure p, with e_p proper and confirming p, e_p(x)<=f(x) for every x in the entire original cone and every original proper confirmer f of p, and e_p(q)=e_q(p) for every pair of pure points. Leastness is required on the whole cone, including nonnormalized positive vectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("least-confirmation-from-circuits"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit_balance_least_confirmation"),
                H("Constructing reciprocal least confirmation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the original closed generating C and strictly positive u, all-reference circuit balance yields real linear effects e_p satisfying six conclusions: e_p is proper and confirms p; e_p(q)=T_q(p); T_p(q)=T_q(p); e_p is least among every original proper confirmer on all of C; T_p(x)=e_p(x) for every x in C; and full S holds for every finite pure list. The identity with the lower envelope is asserted only on C, not on signed vectors outside it.")),
                    Paragraph(Text("The normalized base is closed. On the compact intersection of C with the unit sphere, the continuous unit has a positive minimum; rescaling bounds the norm of every normalized positive vector. The empty-base case is handled directly. Thus the base is compact and convex. Krein–Milman gives that it is the closed convex hull of all its extreme points. The span of those points is closed in finite dimensions, so contains the base; strict-unit rescaling and generatingness give their span equal to A. Closed linear halfspaces similarly extend pure nonnegativity to the base and then to all of C. This proves exactly the spanning and inequality-extension facts needed here without a finite decomposition premise.")),
                    Paragraph(Text("In real coordinates, apply the existing support-contained circuit decomposition to each finite original relation. Balance annihilates every circuit summand, hence every relation, and the existing linear quotient construction descends q maps to T_q(p) to e_p on A. Pure bounds extend through the closed halfspaces, giving 0<=e_p<=u on C and e_p(p)=1. Since the full proper interval includes e_p, T_p(q)<=e_p(q)=T_q(p). Interchanging references supplies the reverse inequality. Pure domination against every confirmer then extends to all of C. Leastness and attainment identify T_p with e_p there, and linearity gives full S."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-equivalence"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.full_mixture_iff_circuit_balance"),
                H("Full comparison is equivalent to circuit balance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the same C and u, full S is equivalent to all-reference circuit balance. That balance is equivalent to its conjunction with pure reciprocity, and to reciprocal least confirming effects on the entire cone. These are the four conditions of Quantum Origin V Theorem 77.16, on the unchanged full state and full proper-effect carrier.")),
                    Paragraph(Text("For the converse, take any finite signed relation sum_i c_i q_i=0 on the original pure points. Applying u gives sum_i c_i=0. Write a_i=max(c_i,0) and b_i=max(-c_i,0); their masses and weighted original vectors agree. Add the same reference p with unit weight to both sides, and divide by the positive common mass 1+sum_i a_i. These are two nonnegative normalized pure preparations of exactly the same vector. Full S evaluates them equally. Cancelling the common reference contribution and common mass proves sum_i c_i T_{q_i}(p)=0, including the zero relation. Reindexing finite types by Fin n introduces no new preparation assumption. Conversely, reciprocal least effects attain the original infimum at every positive vector; their linearity and pure reciprocity give full S."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("descends"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.descends"),
                H("Descent of balanced assignments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every set P spanning A and every scalar assignment balanced on all its finite circuits, there exists an original real linear functional taking those assigned values on every p in P."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pure-mem"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_mem"),
                H("Pure points are normalized positive vectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every pure point belongs to the original cone and has original unit value one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("base-convex"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base_convex"),
                H("Convexity of the normalized base"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The entire normalized base of the original cone and linear unit is convex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-mem"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.normalized_mem"),
                H("Normalization of nonzero positive vectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a unit strictly positive on every nonzero cone vector, multiplying any nonzero vector x in the cone by the inverse of u(x) places it in the entire normalized base. The same theorem applies to native face cones by restricting strict positivity along their inclusion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pure-span"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_span"),
                H("Pure spanning of the original carrier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the compact original base, strictly positive unit and generating original cone, all pure points together linearly span the original carrier."))), DescribeRole.Theorem),
            Paragraph(Text("The circuit-size and two-points-per-sign clauses of Lemma 77.15, the mixed-remainder equivalence of Theorem 77.19, and the EJA, PRE, reset, H13/C13 and static or operational consumers remain outside this result. The proof needs neither a finite Minkowski theorem nor an assumption supplying pure decompositions. Mathematical effects and mixtures do not supply actual preparation programs, menus, histories, references or operations.")))));
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Dual() => Call("LinearMap", Real(), Id("A"), Real());
    private static Formula Base() => Call("base", Id("C"), Id("u"));
    private static Formula Pure() => Call("pure", Id("C"), Id("u"));
    private static Formula Strict() => All("x", Id("A"), Imp(Member(Id("x"), Id("C")),
        Imp(Seq(Id("x"), Neq, Sp, D(0)), Seq(D(0), Lt, Sp, Call("apply", Id("u"), Id("x"))))));
    private static Formula Geo(Formula b) => All("A", Id("Type"), Seq(
        OpenBracket, Call("NormedAddCommGroup", Id("A")), CloseBracket, Sp,
        OpenBracket, Call("NormedSpace", Real(), Id("A")), CloseBracket, Sp,
        OpenBracket, Call("FiniteDimensional", Real(), Id("A")), CloseBracket, Sp,
        All("C", Call("PointedCone", Real(), Id("A")), All("u", Dual(), b))));
    private static DocumentBlock GeometryFact(string name, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/CircuitBalancedConfirmation." + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

}

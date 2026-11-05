using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GeometricMeasure;

internal sealed class SmolinNoisyHilbertSchmidtDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/zhuhuangzhangniezhaolu2026universal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The noisy Smolin state has an attained Hilbert-Schmidt distance for each of four partitions.",
        H("Exact Hilbert-Schmidt distances of noisy Smolin states"),
        Blocks(
            Paragraph(Text(
                "All matrices have complex entries. IsDensity means positive semidefinite with trace one. "
                + "IsSeparable means a finite convex combination of products of density matrices for the two indicated factors. "
                + "The Pauli family sigma has sigma 0 equal to the identity and sigma 1, sigma 2, sigma 3 "
                + "equal to the X, Y, Z Pauli matrices, respectively. Matrix.kroneckerMap with the displayed "
                + "complex multiplication function is the Kronecker product. Scalar multiplication is written with a dot; "
                + "the scalar's type distinguishes real from complex scalar multiplication. DFunLike.coe explicitly "
                + "turns an equivalence into its underlying function.")),
            Node("q", "Q", "Four-qubit coordinates", QFormula(),
                "The four binary coordinates are associated to the right. This fixes the ordering of all four tensor factors.",
                AssessedProvenance.FromRepo()),
            Node("smolin", "smolin", "The Smolin matrix", SmolinFormula(),
                "The Smolin matrix is one sixteenth of the sum of the identity and the three fourfold Pauli products. "
                + "The complex coefficient and the identity matrix are typed explicitly. This is manuscript.tex, lines 657-662.",
                AssessedProvenance.FromLiterature(Source)),
            Node("noisy", "noisy", "Addition of white noise", NoisyFormula(),
                "For any real p, noisy p is the affine combination of the Smolin matrix and the maximally mixed matrix. "
                + "The coefficients p and 1-p act as real scalars. For p in the unit interval this is the noisy state "
                + "of manuscript.tex, lines 669-671; the definition also gives a matrix outside that interval.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sep-one-one-two", "SepOneOneTwo", "Separability for the partition 1:2:34", OneOneTwoFormula(),
                "Take the real convex hull of a tensor product of two one-qubit density matrices and one two-qubit "
                + "density matrix. This is the set separable for the partition {1}:{2}:{3,4} in manuscript.tex, lines 662-666. "
                + "The convex hull consists of finite convex combinations.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sep-full", "SepFull", "Full separability", FullFormula(),
                "Take the real convex hull of tensor products of four one-qubit density matrices, with the same "
                + "right association as Q. This is separability for {1}:{2}:{3}:{4}, the four-partition "
                + "in manuscript.tex, lines 662-666.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sep-two-two", "SepTwoTwo", "Separability for the partition 12:34", TwoTwoFormula(),
                "Reindex both matrix coordinates from (Fin 2 times Fin 2) times (Fin 2 times Fin 2) to Q, "
                + "then require separability between the two pairs. The same product-associating equivalence is "
                + "coerced to a function in each coordinate. This represents the partition {1,2}:{3,4} "
                + "in manuscript.tex, lines 662-668.",
                AssessedProvenance.FromLiterature(Source)),
            Node("hs-dist", "hsDist", "Hilbert-Schmidt distance", DistanceFormula(),
                "For arbitrary matrices X and Y, take the real square root of the real part of the trace of "
                + "(X-Y) conjugate-transpose times (X-Y). The real part is taken before the square root. "
                + "This is the Hilbert-Schmidt distance used in manuscript.tex, lines 662-665.",
                AssessedProvenance.FromLiterature(Source)),
            Node("f", "f", "The proposed distance function", FFormula(),
                "The function is zero at and below one third and is affine with slope square root of three divided "
                + "by four above one third. It is defined for every real p; its restriction to the unit interval "
                + "is the proposed formula in manuscript.tex, lines 672-687.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "The four attained minima", Equal(Named("claim"), Parenthesized(ClaimBody())),
                "For every p in [0,1], the least distance to the states separable for {1}:{2,3,4}, "
                + "{1}:{2}:{3,4}, and {1}:{2}:{3}:{4} is f p. The least distance for {1,2}:{3,4} is zero. "
                + "Each IsLeast assertion includes both attainment and a lower bound for every competing distance. "
                + "These are the three proposed nonzero-distance cases of manuscript.tex, lines 672-687, "
                + "together with the separable case stated at line 668.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("smolin-hs-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact distances and their attaining states"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The distance from a matrix to itself is zero. Tensor products of density matrices remain "
                        + "positive semidefinite and have trace one, and every product of two density matrices is separable. "
                        + "Finite convex combinations of separable matrices are separable: concatenate the two finite "
                        + "product decompositions and multiply their weights by the two outer convex coefficients. "
                        + "Grouping the last two factors therefore gives SepFull contained in SepOneOneTwo, which is "
                        + "contained in the states separable for {1}:{2,3,4}. Grouping the first and last pairs, "
                        + "and reindexing, also gives SepFull contained in SepTwoTwo.")),
                    Paragraph(Text(
                        "The maximally mixed matrix is the product of four copies of the one-qubit density I/2, "
                        + "so it is fully separable. For each Pauli matrix A, the two matrices (I+A)/2 and (I-A)/2 "
                        + "are density matrices. Average the eight fourfold products of these matrices for which "
                        + "the number of minus choices is even. Expanding the products gives (I+A tensor A tensor A tensor A)/16. "
                        + "Averaging these three matrices for A equal to X, Y, Z gives noisy (1/3), so this boundary "
                        + "matrix is fully separable. For 0 ≤ p ≤ 1/3, the identity "
                        + "noisy p = (3p) noisy (1/3) + (1-3p) I/16 expresses noisy p as a convex combination "
                        + "of two fully separable matrices.")),
                    Paragraph(Text(
                        "Write C for the sum of the three fourfold Pauli products. Pauli trace orthogonality gives "
                        + "tr C = 0 and tr(C squared) = 48, hence Re tr(C noisy p) = 3p for every real p. "
                        + "To bound the same linear functional on a product a tensor b, where a is a one-qubit "
                        + "density and b is a three-qubit density, let B_j be the threefold product of the jth "
                        + "Pauli matrix. These three matrices are Hermitian involutions and anticommute in pairs. "
                        + "For arbitrary real coefficients t_j their weighted sum has square (sum of t_j squared) I.")),
                    Paragraph(Text(
                        "Now set t_j = Re tr(B_j b), T = sum of t_j B_j, and q = sum of t_j squared. "
                        + "Then T is Hermitian, T squared equals qI, and Re tr(Tb) = q. Positivity of "
                        + "tr((T-I) conjugate-transpose (T-I) b) yields 0 ≤ q-2q+1, so q ≤ 1. "
                        + "The Bloch vector r of a has sum of r_j squared at most one, and its Pauli expectations "
                        + "are r_j. Thus Re tr(C(a tensor b)) = sum of r_j t_j ≤ 1 by Cauchy-Schwarz. "
                        + "Applying this bound to each product in a finite convex decomposition proves "
                        + "Re tr(C sigma) ≤ 1 for every state sigma separable for {1}:{2,3,4}.")),
                    Paragraph(Text(
                        "The Hilbert-Schmidt trace-product inequality gives "
                        + "Re tr(CX) ≤ square root of 48 times hsDist X 0 for every complex matrix X. "
                        + "Indeed, reindex to a finite numerical index set, apply the squared trace-product bound, "
                        + "use C conjugate-transpose equal to C and tr(C squared) = 48, and use positivity of "
                        + "tr(X conjugate-transpose X). Dropping the squared imaginary part bounds the squared real part; "
                        + "taking square roots bounds its absolute value and hence its real part. With X = noisy p - sigma, "
                        + "the separable expectation bound gives 3p-1 ≤ square root of 48 times hsDist (noisy p) sigma. "
                        + "For p > 1/3 this is f p ≤ hsDist (noisy p) sigma, since square root of 48 equals four "
                        + "times square root of three. For p ≤ 1/3 the same distance lower bound is simply nonnegativity.")),
                    Paragraph(Text(
                        "The difference noisy p - noisy (1/3) equals ((p-1/3)/16) C. Its squared "
                        + "Hilbert-Schmidt norm is ((p-1/3)/16) squared times 48. Taking the real square root "
                        + "gives hsDist (noisy p) (noisy (1/3)) = (square root of three divided by four) times |p-1/3|.")),
                    Paragraph(Text(
                        "For the two-pair partition, let Pi_mu, with mu in Fin 4, be the four Bell projectors. "
                        + "Each Pauli expansion is one quarter of the sum of I and signed XX, YY, ZZ terms, with sign rows "
                        + "(1,-1,1), (-1,1,1), (1,1,-1), (-1,-1,-1). Each projector is a unitary "
                        + "conjugate of the normalized Bell density by I tensor I, Z tensor I, X tensor I, "
                        + "or Y tensor I, respectively. Unitary conjugation preserves positive semidefiniteness, "
                        + "and cyclicity of the trace gives trace one. "
                        + "After associating the coordinates into two pairs, expansion and cancellation of the sign terms "
                        + "give smolin = one quarter of the sum of Pi_mu tensor Pi_mu. This is a separable decomposition "
                        + "for {1,2}:{3,4}. For p in [0,1], combining it with I/16 using weights p and 1-p proves "
                        + "noisy p belongs to SepTwoTwo.")),
                    Paragraph(Text(
                        "Finally, let K contain SepFull and be contained in the states separable for {1}:{2,3,4}. "
                        + "For p ≤ 1/3, choose noisy p in K and use its zero distance to itself. For p > 1/3, "
                        + "choose noisy (1/3) in K and use the boundary distance formula. The lower bound holds for "
                        + "every matrix in K, proving that f p is its least attainable distance. Apply this first "
                        + "to the states separable for {1}:{2,3,4}, then to SepOneOneTwo, then to SepFull. "
                        + "For SepTwoTwo, choose noisy p itself to attain zero; nonnegativity of every "
                        + "Hilbert-Schmidt distance proves the remaining lower bound."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhu-huang-zhang-nie-zhao-lu-2026-smolin-hilbert-schmidt-distance"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("smolin-hs-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinTwo => Call("Fin", D(2));
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, Parenthesized(right));
    private static Formula Pair => Product(FinTwo, FinTwo);
    private static Formula Q => F.Id("Q");
    private static Formula Mat(Formula index) => Call("Matrix", index, index, Complexes);
    private static Formula MatQ => Mat(Q);
    private static Formula P => F.Id("p");
    private static Formula Noisy(Formula p) => Call("noisy", p);
    private static Formula Distance(Formula x, Formula y) => Call("hsDist", x, y);
    private static Formula Third => new Formula.Fraction(Typed(D(1), Reals), Typed(D(3), Reals));
    private static Formula ComplexSixteenth => new Formula.Fraction(Typed(D(1), Complexes), Typed(D(1, 6), Complexes));
    private static Formula Identity => Typed(D(1), MatQ);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(Variable(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(Variable(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Variable(string name) => name switch
    {
        "ρ" => Rho,
        "σ" => SigmaLower,
        _ => F.Id(name),
    };
    private static Formula SetOf(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, Typed(Variable(name), type), Sp, Mid, Sp, Parenthesized(predicate), CloseBrace);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula PlusOf(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula MinusOf(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Kron(Formula left, Formula right)
    {
        Formula x1 = Seq(Operatorname, Grp(F.Id("x"), D(1)));
        Formula x2 = Seq(Operatorname, Grp(F.Id("x"), D(2)));
        Formula multiplication = Seq(LambdaLower, Sp, Typed(x1, Complexes),
            Sp, Typed(x2, Complexes), Sp, Mapsto, Sp, Parenthesized(Mul(x1, x2)));
        return App(Qualified("Matrix", "kroneckerMap"), Parenthesized(multiplication), left, right);
    }
    private static Formula Density(string name) => Call("IsDensity", F.Id(name));
    private static Formula ConvexHull(Formula set) => App(Named("convexHull"), Reals, set);
    private static Formula Pauli(byte j) => Call("sigma", Typed(D(j), Call("Fin", D(4))));
    private static Formula PauliProduct(byte j) => Kron(Pauli(j), Kron(Pauli(j), Kron(Pauli(j), Pauli(j))));

    private static Formula QFormula() => Equal(Q, Product(FinTwo, Product(FinTwo, Pair)));
    private static Formula SmolinFormula() => Equal(Typed(Named("smolin"), MatQ),
        Smul(ComplexSixteenth, PlusOf(Identity, PlusOf(PlusOf(PauliProduct(1), PauliProduct(2)), PauliProduct(3)))));
    private static Formula NoisyFormula() => All("p", Reals, Equal(Typed(Noisy(P), MatQ),
        PlusOf(Smul(P, Named("smolin")),
            Smul(MinusOf(Typed(D(1), Reals), P), Smul(ComplexSixteenth, Identity)))));
    private static Formula OneOneTwoFormula() => Equal(Typed(Named("SepOneOneTwo"), Call("Set", MatQ)),
        ConvexHull(SetOf("ρ", MatQ, Some("a", Mat(FinTwo), Some("b", Mat(FinTwo), Some("c", Mat(Pair),
            And(Density("a"), And(Density("b"), And(Density("c"),
                Equal(Rho, Kron(F.Id("a"), Kron(F.Id("b"), F.Id("c")))))))))))));
    private static Formula FullFormula() => Equal(Typed(Named("SepFull"), Call("Set", MatQ)),
        ConvexHull(SetOf("ρ", MatQ, Some("a", Mat(FinTwo), Some("b", Mat(FinTwo),
            Some("c", Mat(FinTwo), Some("d", Mat(FinTwo),
                And(Density("a"), And(Density("b"), And(Density("c"), And(Density("d"),
                    Equal(Rho, Kron(F.Id("a"), Kron(F.Id("b"), Kron(F.Id("c"), F.Id("d"))))))))))))))));
    private static Formula TwoTwoFormula()
    {
        Formula association = App(Qualified("Equiv", "prodAssoc"), FinTwo, FinTwo, Pair);
        Formula function = App(Qualified("DFunLike", "coe"), association);
        return Equal(Typed(Named("SepTwoTwo"), Call("Set", MatQ)), SetOf("ρ", MatQ,
            Call("IsSeparable", App(Qualified("Matrix", "submatrix"), Rho, function, function))));
    }
    private static Formula DistanceFormula()
    {
        Formula difference = MinusOf(F.Id("X"), F.Id("Y"));
        Formula trace = App(Qualified("Matrix", "trace"),
            Mul(App(Qualified("Matrix", "conjTranspose"), difference), difference));
        return All("X", MatQ, All("Y", MatQ, Equal(Typed(Distance(F.Id("X"), F.Id("Y")), Reals),
            App(Qualified("Real", "sqrt"), App(Qualified("Complex", "re"), trace)))));
    }
    private static Formula FFormula() => All("p", Reals, Equal(Typed(Call("f", P), Reals),
        Call("ite", new Formula.Relation(P, FormulaRelationOperator.LessThanOrEqual, Third), Typed(D(0), Reals),
            Mul(new Formula.Fraction(App(Qualified("Real", "sqrt"), Typed(D(3), Reals)), Typed(D(4), Reals)),
                MinusOf(P, Third)))));
    private static Formula LeastDistance(Formula condition, Formula value) =>
        Call("IsLeast", SetOf("d", Reals, Some("σ", MatQ,
            And(condition, Equal(F.Id("d"), Distance(Noisy(P), SigmaLower))))), value);
    private static Formula ClaimBody() => All("p", Reals, Implies(
        Member(P, App(Qualified("Set", "Icc"), Typed(D(0), Reals), Typed(D(1), Reals))),
        And(LeastDistance(Call("IsSeparable", SigmaLower), Call("f", P)),
            And(LeastDistance(Member(SigmaLower, Named("SepOneOneTwo")), Call("f", P)),
                And(LeastDistance(Member(SigmaLower, Named("SepFull")), Call("f", P)),
                    LeastDistance(Member(SigmaLower, Named("SepTwoTwo")), Typed(D(0), Reals)))))));
}

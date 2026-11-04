using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class IptPptSquaredEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/chiribelladavidsonpaulsenrahaman2023real");
    private static readonly LibraryNoteRef Flags =
        LibraryNoteRef.Create("D5/L/QuantumChannels/huberlamilancienmullerhermes2018ppt");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complex PPT-squared conjecture is equivalent to the IPT-squared conjectures over the complex and real fields. The reverse implications use a two-dimensional flag and preserve composition.",
        H("Equivalence of PPT-squared and IPT-squared"),
        Blocks(
            OwnerNode("kron", "D5/S3/Quantum/Foundation/FiniteKrausChannel.kron", "Amplification", Amplification(),
                "MatrixMap.kron supplies the amplification Phi tensor the identity on Fin r; kron_id_apply gives the displayed coordinate expression. The scalar K represents the Lean parameter 𝕜 with its RCLike instance. All indices use Fin; ordered pairs put the map's factor first. This is the coordinate encoding of Section 8, PDF p. 18.",
                DescribeRole.Definition, Lit()),
            Node("kron_id_apply", "Coordinates of an identity amplification", KronIdApply(),
                "Over every RCLike field 𝕜 and all finite input, output and ancillary dimensions, amplifying a linear matrix map Phi by the identity applies Phi to each matrix slice with the ancillary indices fixed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("ampl_kron", "Identity amplification on a product matrix", AmplKron(),
                "For every RCLike field and finite system and ancillary dimensions, identity amplification sends the product A tensor B to Phi(A) tensor B.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            OwnerNode("cp", "D5/S3/Quantum/Foundation/FiniteKrausChannel.IsCompletelyPositive", "Complete positivity", PositivePredicate(false),
                "MatrixMap.IsCompletelyPositive states that a map is completely positive when every amplification preserves positive semidefiniteness. Matrix.PosSemidef is the pinned matrix predicate. Quantification includes r = 0; that case contains only the empty matrix.",
                DescribeRole.Definition, Lit()),
            Node("SEP", "Separable cone", Separability(),
                "Section 6 defines the separable cone by finite sums of products of rank-one positive matrices. Nonnegative coefficients are absorbed into the vectors. The displayed finite sum runs over all j : Fin k. Matrix.kroneckerMap uses scalar multiplication of entries, and star acts pointwise on each vector.",
                DescribeRole.Definition, Lit()),
            Node("IsEB", "Entanglement breaking", PositivePredicate(true),
                "Section 8, PDF p. 18: \"For p = 1, we just call the map Φ 𝕂-entanglement breaking.\" Its preceding condition is (Φ ⊗ idᵣ)(P) ∈ SEPₚ(𝕂ᵐ ⊗ 𝕂ʳ) for all positive P and r ≥ 1. The display specializes p to one and adds only the vacuous empty amplification. No trace-preserving or unital condition is imposed.",
                DescribeRole.Definition, Lit()),
            OwnerNode("choi", "D5/S3/Quantum/Foundation/FiniteKrausRepresentation.choi_matrix", "Input-first Choi matrix", Choi(),
                "MatrixMap.choi_matrix supplies the displayed output-first coordinate expression; submatrix Prod.swap Prod.swap puts the input factor first. Applying Phi to the matrix unit Matrix.single a.1 b.1 1 gives its entry at output indices a.2 and b.2. The canonical Kraus Choi matrix places output first; Prod.swap relates the two tensor orders.",
                DescribeRole.Definition, Lit()),
            OwnerNode("choi-psd-of-cp", Prefix + "choi_psd_of_cp",
                "Complete positivity gives Choi positivity", ChoiPositive(),
                "For every RCLike scalar field K and all natural dimensions n and m, a completely positive K-linear map Phi from n by n matrices to m by m matrices has a positive semidefinite input-first Choi matrix. The input-first matrix is MatrixMap.choi_matrix Phi with both indices composed with Prod.swap. The IPT-to-PPT implication uses this positivity, and swapping the tensor factors again gives the output-first positivity used for qubit channels.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("ptFirst", "Partial transpose on the first factor", PartialTranspose(),
                "The first coordinates are exchanged and the second coordinates retained. This is τₙ tensor idₘ in Section 9.1, PDF p. 21; it is an ordinary transpose without complex conjugation.",
                DescribeRole.Definition, Lit()),
            Node("IsPPT", "PPT maps", MapPredicate(false),
                "Section 9.1, PDF p. 21: \"A completely positive map Φ : Mₙ(𝕂) → Mₘ(𝕂) is called PPT (IPT) if its Choi matrix is PPT (IPT).\" Here PPT requires the first-factor partial transpose of the Choi matrix to be positive semidefinite.",
                DescribeRole.Definition, Lit()),
            Node("IsIPT", "IPT maps", MapPredicate(true),
                "Section 9.1, PDF p. 21: \"A completely positive map Φ : Mₙ(𝕂) → Mₘ(𝕂) is called PPT (IPT) if its Choi matrix is PPT (IPT).\" Here IPT requires equality of the Choi matrix with its first-factor partial transpose.",
                DescribeRole.Definition, Lit()),
            Node("PPT2C", "The complex PPT-squared conjecture", ComplexConjecture(),
                "Conjecture 9.5, PDF p. 23: \"For every PPT map Φ : Mₙ(ℂ) → Mₙ(ℂ), Φ ◦ Φ is ℂ-entanglement breaking.\" The dimension n is universally quantified. The linear-map composition Phi ∘ₗ Phi is the square.",
                DescribeRole.Definition, Lit()),
            Node("IPT2", "The IPT-squared conjecture", IptConjecture(),
                "Conjecture 9.7, PDF p. 24: \"For 𝕂 ∈ {ℝ, ℂ}, every IPT map Φ : Mₙ(𝕂) → Mₙ(𝕂) satisfies Φ ◦ Φ is 𝕂-entanglement breaking.\" The definition is generic over RCLike K and is used at ℝ and ℂ. Zero dimension adds only a vacuous case.",
                DescribeRole.Definition, Lit()),
            Node("claim", "The equivalence question", Disp(IffOf(V("claim"), Equivalence())),
                "Section 9.2, after Proposition 9.9, PDF p. 25: \"We do not know if these conjectures are equivalent.\" The encoding is the conjunction (PPT2C ↔ IPT2 ℂ) ∧ (IPT2 ℂ ↔ IPT2 ℝ). Each conjecture ranges over all dimensions; this does not assert that the conjectures themselves are true.",
                DescribeRole.Definition, Lit()),
            Describe.Remark(DescribeId.Create("flag-lift"), H("A composition-compatible flag"), FlagConstruction(),
                AssessedProvenance.FromLiterature(Flags), Blocks(Paragraph(Text(
                    "On the auxiliary two-dimensional factor take P+ = (1,i)(1,i)*/2 and P- = (1,-i)(1,-i)*/2. Their transpose exchanges them. Compress to these flag sectors with B+ and B-, and put E(X) = B+(X) + B-(X)^T and D(A) = A tensor P+ + A^T tensor P-. The lift D Phi E/2 has four completely positive branches for every complex PPT Phi. It is invariant under transpose on input and output, so its real restriction is IPT and complexifies back to the lift. The identity E D = 2 id makes the lift preserve composition. Completely positive insertion A tensor P+ and compression B+ recover Phi squared divided by two. This transfers entanglement breaking from the lifted square. The lift adapts the conjugate-flag construction rho tensor P+ + rho partially transposed tensor P- of Huber, Lami, Lancien and Müller-Hermes, arXiv v1, Section III.C, PDF p. 8, the second lemma labelled III.1. The map normalization, composition law and recovery are the consequences used here.")))),
            Node("IsSeparable", "Normalized finite separable mixtures", NormalizedMixture(),
                "A separable bipartite matrix is a finite convex mixture of tensor products of positive semidefinite trace-one matrices. The two index types are arbitrary finite types.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("weighted", "The conditional ancillary matrix", WeightedFormula(false),
                "The effect M is paired by trace with each system slice of P; the remaining two coordinates index the ancillary matrix.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            OwnerNode("weighted-psd", Prefix + "weighted_psd", "Positive conditional ancillary matrices", WeightedFormula(true),
                "A positive effect and a positive joint input give a positive conditional ancillary matrix, by rank-one decomposition and positive congruence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("HasPrepare", "Finite positive measure-and-prepare form", PrepareFormula(),
                "A finite family of positive measurement matrices M and positive preparation matrices N represents Phi by the sum of trace(M(j) A) times N(j), for every input matrix A. The natural number k counts all terms; n and m are arbitrary input and output dimensions over an RCLike scalar field K. Scalar multiplication is displayed by a centered dot.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            OwnerNode("prepare-eb", Prefix + "prepare_eb", "Positive measure-and-prepare maps break entanglement", PrepareBreaking(),
                "Every positive amplified input has separable output under a map with finite positive measure-and-prepare form. Positivity of each weighted matrix follows from a rank-one decomposition of the measurement matrix and positive congruence of the input; tensor products with the positive preparations then form a finite separable sum.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("cp_comp", "Composition preserves complete positivity", CpComposition(),
                "The composition of completely positive linear matrix maps is completely positive, over every RCLike field and all finite dimensions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("cp_double_tau", "Double transposition preserves complete positivity", CpDoubleTranspose(),
                "For every completely positive complex-linear matrix map, transposing its input and output gives a completely positive map. Input and output dimensions may differ.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "The three conjectures are equivalent", Disp(Equivalence()),
                "IPT² over either field in dimension 2n implies PPT² over ℂ in dimension n by the flag lift and recovery. The source's implications PPT²(ℂ) ⇒ IPT²(ℂ) ⇒ IPT²(ℝ) retain dimension n. Entanglement breaking is characterized by a separable input-first Choi matrix, with an explicit tensor swap, and by measure-and-prepare form. Completely positive maps preserve it under pre- and post-composition. The complexification of a real entanglement-breaking map is complex entanglement breaking; in the reverse direction the IPT condition gives CSEP ∩ IPT = real SEP. These facts close both equivalences. The PPT-squared conjecture itself and the possibility of avoiding dimension doubling remain open.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chiribella-davidson-paulsen-rahaman-2023-ppt-ipt-squared-equivalence"),
                    ResolutionKind.Proved)))));

    private static Formula Cp(Formula phi) => App(Qualified("MatrixMap", "IsCompletelyPositive"), phi);
    private static Formula RectMap(Formula scalar, string input, string output) => Seq(Mat(FinOf(V(input)), scalar), Sp,
        new Formula.Subscript(To, Seq(V("l"), OpenBracket, scalar, CloseBracket)), Sp, Mat(FinOf(V(output)), scalar));
    private static Formula LinearCompose(Formula a, Formula b) => Seq(Parenthesized(a), Sp, new Formula.Subscript(Circ, V("l")), Sp, Parenthesized(b));
    private static Formula TransposeMap(string d) => App(Qualified("LinearEquiv", "toLinearMap"),
        App(Qualified("Matrix", "transposeLinearEquiv"), FinOf(V(d)), FinOf(V(d)), C, C));
    private static Formula CpComposition() => Disp(All("K", Named("Type"), Instance(All("n", N, All("m", N, All("p", N,
        All("Phi", RectMap(V("K"), "m", "p"), All("Psi", RectMap(V("K"), "n", "m"),
        Imp(Cp(V("Phi")), Imp(Cp(V("Psi")), Cp(LinearCompose(V("Phi"), V("Psi")))))))))))));
    private static Formula CpDoubleTranspose() => Disp(All("n", N, All("m", N, All("Phi", RectMap(C, "n", "m"),
        Imp(Cp(V("Phi")), Cp(LinearCompose(TransposeMap("m"), LinearCompose(V("Phi"), TransposeMap("n")))))))));

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("ipt-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static DocumentBlock OwnerNode(string id, string owner, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("ipt-" + id), DeclarationHandle.Create(owner), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Amplified(Formula phi, Formula r, Formula matrix) => App(
        App(Qualified("MatrixMap", "kron"), phi,
            Seq(Qualified("LinearMap", "id"), Colon, Call("MatrixMap", FinOf(r), FinOf(r), V("K")))), matrix);
    private static Formula SourceChoi(Formula phi)
    {
        Formula indices = ProdOf(FinOf(V("m")), FinOf(V("n")));
        Formula unit = App(Qualified("Matrix", "single"),
            Component("j", 2), Component("k", 2), D(1));
        Formula ownedBody = Fun("j", indices, Fun("k", indices,
            App(App(phi, unit), Component("j", 1), Component("k", 1))));
        return App(Qualified("Matrix", "submatrix"), Parenthesized(ownedBody),
            Qualified("Prod", "swap"), Qualified("Prod", "swap"));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula body) => Seq(OpenBracket, Call("RCLike", V("K")), CloseBracket, Sp, body);
    private static Formula EqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula FinOf(Formula size) => Call("Fin", size);
    private static Formula ProdOf(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Mat(Formula indices, Formula scalar) => Call("Matrix", indices, indices, scalar);
    private static Formula TensorMatrix(string left, string right) => Mat(ProdOf(FinOf(V(left)), FinOf(V(right))), V("K"));
    private static Formula MapOf(Formula scalar) => Seq(Mat(FinOf(V("n")), scalar), Sp,
        new Formula.Subscript(To, Seq(V("l"), OpenBracket, scalar, CloseBracket)), Sp, Mat(FinOf(V("m")), scalar));
    private static Formula EndOf(Formula scalar) => Seq(Mat(FinOf(V("n")), scalar), Sp,
        new Formula.Subscript(To, Seq(V("l"), OpenBracket, scalar, CloseBracket)), Sp, Mat(FinOf(V("n")), scalar));
    private static Formula Generic(Formula body) => All("K", Named("Type"), Instance(All("n", N, All("m", N, body))));
    private static Formula Component(string value, byte field) => Seq(V(value), Dot, D(field));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Psd(Formula matrix) => App(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula Square(Formula phi) => Seq(phi, Sp, new Formula.Subscript(Circ, V("l")), Sp, phi);

    private static Formula WeightedFormula(bool positivity)
    {
        Formula m = V("M"), p = V("P");
        Formula slice = Fun("i", FinOf(V("n")), Fun("j", FinOf(V("n")),
            App(p, Pair(V("i"), V("u")), Pair(V("j"), V("v")))));
        Formula trace = App(Qualified("Matrix", "trace"), Parenthesized(Seq(m, Star, Parenthesized(slice))));
        Formula body = positivity ? Imp(Psd(m), Imp(Psd(p), Psd(Call("weighted", m, p))))
            : EqTo(Call("weighted", m, p), Fun("u", FinOf(V("r")), Fun("v", FinOf(V("r")), trace)));
        return Disp(All("K", Named("Type"), Instance(All("n", N, All("r", N,
            All("M", Mat(FinOf(V("n")), V("K")), All("P", TensorMatrix("n", "r"), body)))))));
    }
    private static Formula NormalizedMixture()
    {
        Formula n = V("n"), i = V("i"), p = V("p"), x = V("X"), y = V("Y");
        Formula S(Formula t) => Mat(t, C);
        Formula Density(Formula t) => And(Psd(t), EqTo(App(Qualified("Matrix", "trace"), t), D(1)));
        Formula SumOf(Formula t) => Seq(Sum, Underscore, Grp(i, Colon, FinOf(n)), Sp, Parenthesized(t));
        Formula si = App(V("sigma"), i), ti = App(V("tau"), i);
        Formula weight = Parenthesized(Seq(App(p, i), Colon, Sp, C));
        Formula tensor = App(Qualified("Matrix", "kronecker"), si, ti);
        Formula rhs = Ex("n", N, Ex("p", new Formula.TypeArrow(FinOf(n), R),
            Ex("sigma", new Formula.TypeArrow(FinOf(n), S(x)),
            Ex("tau", new Formula.TypeArrow(FinOf(n), S(y)),
            And(All("i", FinOf(n), new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, App(p, i))),
            And(EqTo(SumOf(App(p, i)), D(1)),
            And(All("i", FinOf(n), And(Density(si), Density(ti))),
                EqTo(V("rho"), SumOf(App(Qualified("HSMul", "hSMul"), weight, tensor))))))))));
        Formula Class(Formula t, Formula b) => Seq(OpenBracket, Call("Fintype", t), CloseBracket, Sp, b);
        return Disp(All("X", Named("Type"), Class(x, All("Y", Named("Type"), Class(y,
            All("rho", S(ProdOf(x, y)), IffOf(Call("IsSeparable", V("rho")), rhs)))))));
    }

    private static Formula Amplification()
    {
        Formula a1 = Component("a", 1), a2 = Component("a", 2), b1 = Component("b", 1), b2 = Component("b", 2);
        Formula slice = Fun("i", FinOf(V("n")), Fun("j", FinOf(V("n")), App(V("P"), Pair(V("i"), a2), Pair(V("j"), b2))));
        Formula body = Fun("a", ProdOf(FinOf(V("m")), FinOf(V("r"))),
            Fun("b", ProdOf(FinOf(V("m")), FinOf(V("r"))), App(App(V("Phi"), Parenthesized(slice)), a1, b1)));
        return Disp(Generic(All("Phi", MapOf(V("K")), All("r", N, All("P", TensorMatrix("n", "r"),
            EqTo(Amplified(V("Phi"), V("r"), V("P")), body))))));
    }

    private static Formula KronIdApply()
    {
        Formula field = Seq(Mathbb, Grp(V("k")));
        Formula indices = ProdOf(FinOf(V("m")), FinOf(V("r")));
        Formula slice = Fun("i", FinOf(V("n")), Fun("j", FinOf(V("n")),
            App(V("P"), Pair(V("i"), Component("a", 2)), Pair(V("j"), Component("b", 2)))));
        Formula identity = Parenthesized(Seq(Qualified("LinearMap", "id"), Colon, Sp,
            Call("MatrixMap", FinOf(V("r")), FinOf(V("r")), field)));
        Formula amplified = App(Qualified("MatrixMap", "kron"), V("Phi"), identity);
        Formula coordinates = EqTo(App(amplified, V("P"), V("a"), V("b")),
            App(App(V("Phi"), Parenthesized(slice)), Component("a", 1), Component("b", 1)));
        Formula body = All("n", N, All("m", N, All("Phi", MapOf(field), All("r", N,
            All("P", Mat(ProdOf(FinOf(V("n")), FinOf(V("r"))), field),
            All("a", indices, All("b", indices, coordinates)))))));
        return Disp(Seq(Forall, Sp, Parenthesized(Seq(field, Colon, Sp, Named("Type"))),
            Comma, Sp, OpenBracket, Call("RCLike", field), CloseBracket, Sp, body));
    }

    private static Formula AmplKron()
    {
        Formula phi = V("Phi"), a = V("A"), b = V("B");
        Formula kron(Formula left, Formula right) => App(Qualified("Matrix", "kronecker"), left, right);
        Formula conclusion = EqTo(Amplified(phi, V("r"), kron(a, b)), kron(App(phi, a), b));
        return Disp(Generic(All("Phi", MapOf(V("K")), All("r", N,
            All("A", Mat(FinOf(V("n")), V("K")),
            All("B", Mat(FinOf(V("r")), V("K")), conclusion))))));
    }

    private static Formula PositivePredicate(bool breaking)
    {
        Formula image = Amplified(V("Phi"), V("r"), V("P"));
        Formula conclusion = breaking ? Member(image, Call("SEP", V("K"), V("m"), V("r"))) : Psd(image);
        Formula body = All("r", N, All("P", TensorMatrix("n", "r"), Imp(Psd(V("P")), conclusion)));
        return Disp(Generic(All("Phi", MapOf(V("K")), IffOf(breaking ? Call("IsEB", V("Phi")) : App(Qualified("MatrixMap", "IsCompletelyPositive"), V("Phi")), body))));
    }

    private static Formula Separability()
    {
        Formula j = V("j"), xj = App(V("x"), j), yj = App(V("y"), j);
        Formula xr = App(Qualified("Matrix", "vecMulVec"), xj, Call("star", xj));
        Formula yr = App(Qualified("Matrix", "vecMulVec"), yj, Call("star", yj));
        Formula mul = Fun("a", V("K"), Fun("b", V("K"), Seq(V("a"), Sp, Star, Sp, V("b"))));
        Formula sum = Seq(Sum, Underscore, Grp(j, Colon, FinOf(V("k"))), Sp,
            Parenthesized(App(Qualified("Matrix", "kroneckerMap"), Parenthesized(mul), xr, yr)));
        Formula predicate = Ex("k", N, Ex("x", new Formula.TypeArrow(FinOf(V("k")), new Formula.TypeArrow(FinOf(V("m")), V("K"))),
            Ex("y", new Formula.TypeArrow(FinOf(V("k")), new Formula.TypeArrow(FinOf(V("r")), V("K"))), EqTo(V("X"), sum))));
        Formula set = Seq(OpenBrace, V("X"), Colon, TensorMatrix("m", "r"), Sp, Mid, Sp, predicate, CloseBrace);
        return Disp(All("K", Named("Type"), Instance(All("m", N, All("r", N,
            EqTo(Call("SEP", V("K"), V("m"), V("r")), set))))));
    }

    private static Formula Choi()
    {
        Formula unit = App(Qualified("Matrix", "single"), Component("a", 1), Component("b", 1), D(1));
        Formula body = Fun("a", ProdOf(FinOf(V("n")), FinOf(V("m"))),
            Fun("b", ProdOf(FinOf(V("n")), FinOf(V("m"))), App(App(V("Phi"), unit), Component("a", 2), Component("b", 2))));
        return Disp(Generic(All("Phi", MapOf(V("K")), EqTo(SourceChoi(V("Phi")), body))));
    }

    private static Formula PrepareFormula()
    {
        Formula input = Mat(FinOf(V("n")), V("K"));
        Formula output = Mat(FinOf(V("m")), V("K"));
        Formula mj = App(V("M"), V("j")), nj = App(V("N"), V("j"));
        Formula trace = App(Qualified("Matrix", "trace"), Parenthesized(Seq(mj, Sp, Star, Sp, V("A"))));
        Formula sum = Seq(Sum, Underscore, Grp(V("j"), Colon, FinOf(V("k"))), Sp,
            Parenthesized(Seq(trace, Sp, Cdot, Sp, nj)));
        Formula positivity = All("j", FinOf(V("k")), And(Psd(mj), Psd(nj)));
        Formula identity = All("A", input, EqTo(App(V("Phi"), V("A")), sum));
        Formula body = Ex("k", N, Ex("M", new Formula.TypeArrow(FinOf(V("k")), input),
            Ex("N", new Formula.TypeArrow(FinOf(V("k")), output), And(positivity, identity))));
        return Disp(Generic(All("Phi", MapOf(V("K")), IffOf(Call("HasPrepare", V("Phi")), body))));
    }

    private static Formula PrepareBreaking() => Disp(Generic(All("Phi", MapOf(V("K")),
        Imp(Call("HasPrepare", V("Phi")), Call("IsEB", V("Phi"))))));

    private static Formula ChoiPositive() => Disp(Generic(All("Phi", MapOf(V("K")),
        Imp(App(Qualified("MatrixMap", "IsCompletelyPositive"), V("Phi")), Psd(SourceChoi(V("Phi")))))));

    private static Formula PartialTranspose()
    {
        Formula body = Fun("a", ProdOf(FinOf(V("n")), FinOf(V("m"))),
            Fun("b", ProdOf(FinOf(V("n")), FinOf(V("m"))), App(V("X"), Pair(Component("b", 1), Component("a", 2)),
                Pair(Component("a", 1), Component("b", 2)))));
        return Disp(All("K", Named("Type"), All("n", N, All("m", N,
            All("X", TensorMatrix("n", "m"), EqTo(Call("ptFirst", V("X")), body))))));
    }

    private static Formula MapPredicate(bool invariant)
    {
        Formula choi = SourceChoi(V("Phi")), pt = Call("ptFirst", choi);
        Formula body = And(App(Qualified("MatrixMap", "IsCompletelyPositive"), V("Phi")), invariant ? EqTo(pt, choi) : Psd(pt));
        return Disp(Generic(All("Phi", MapOf(V("K")), IffOf(Call(invariant ? "IsIPT" : "IsPPT", V("Phi")), body))));
    }

    private static Formula ConjectureBody(Formula scalar, bool invariant) => All("n", N, All("Phi", EndOf(scalar),
        Imp(Call(invariant ? "IsIPT" : "IsPPT", V("Phi")), Call("IsEB", Parenthesized(Square(V("Phi")))))));
    private static Formula FlagConstruction()
    {
        Formula ab = ProdOf(FinOf(V("n")), FinOf(V("m")));
        Formula flag = Mat(FinOf(D(2)), C);
        Formula plus = Pair(D(1), Qualified("Complex", "I"));
        Formula minus = Pair(D(1), Seq(Minus, Qualified("Complex", "I")));
        Formula pplus = Seq(Frac, Grp(Parenthesized(Seq(plus, Sp,
            new Formula.Power(Parenthesized(plus), Star)))), Grp(D(2)));
        Formula pminus = Seq(Frac, Grp(Parenthesized(Seq(minus, Sp,
            new Formula.Power(Parenthesized(minus), Star)))), Grp(D(2)));
        Formula pt = new Formula.Power(Parenthesized(V("rho")),
            new Formula.Subscript(Gamma, Named("B")));
        Formula liftedPt = new Formula.Power(Parenthesized(V("rhotilde")),
            new Formula.Subscript(Gamma, Seq(Named("B"), Named("B"), Apos)));
        Formula mul = Fun("a", C, Fun("b", C, Seq(V("a"), Sp, Star, Sp, V("b"))));
        Formula construction = Seq(Parenthesized(App(Qualified("Matrix", "kroneckerMap"),
                Parenthesized(mul), V("rho"), V("Pplus"))),
            Sp, Plus, Sp, Parenthesized(App(Qualified("Matrix", "kroneckerMap"),
                Parenthesized(mul), Parenthesized(pt), V("Pminus"))));
        Formula conclusion = Ex("rhotilde", Mat(Parenthesized(ProdOf(Parenthesized(ab), FinOf(D(2)))), C),
            And(EqTo(V("rhotilde"), Parenthesized(construction)),
                And(Psd(V("rhotilde")), EqTo(liftedPt, V("rhotilde")))));
        return Disp(All("n", N, All("m", N, All("rho", Mat(Parenthesized(ab), C),
            All("Pplus", flag, All("Pminus", flag,
                Imp(And(EqTo(V("Pplus"), pplus), EqTo(V("Pminus"), pminus)),
                    Imp(And(Psd(V("rho")), Psd(Parenthesized(pt))), conclusion))))))));
    }
    private static Formula ComplexConjecture() => Disp(IffOf(V("PPT2C"), ConjectureBody(C, false)));
    private static Formula IptConjecture() => Disp(All("K", Named("Type"), Instance(IffOf(Call("IPT2", V("K")), ConjectureBody(V("K"), true)))));
    private static Formula Equivalence() => And(IffOf(V("PPT2C"), Call("IPT2", C)), IffOf(Call("IPT2", C), Call("IPT2", R)));
}

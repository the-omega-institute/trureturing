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
            Node("ampl", "Amplification", Amplification(),
                "The amplification is Phi tensor the identity on Fin r. The scalar K represents the Lean parameter 𝕜 with its RCLike instance. All indices use Fin; ordered pairs put the map's factor first. This is the coordinate encoding of Section 8, PDF p. 18.",
                DescribeRole.Definition, Lit()),
            Node("IsCP", "Complete positivity", PositivePredicate(false),
                "A map is completely positive when every amplification preserves positive semidefiniteness. Matrix.PosSemidef is the pinned matrix predicate. Quantification includes r = 0; that case contains only the empty matrix.",
                DescribeRole.Definition, Lit()),
            Node("SEP", "Separable cone", Separability(),
                "Section 6 defines the separable cone by finite sums of products of rank-one positive matrices. Nonnegative coefficients are absorbed into the vectors. The displayed finite sum runs over all j : Fin k. Matrix.kroneckerMap uses scalar multiplication of entries, and star acts pointwise on each vector.",
                DescribeRole.Definition, Lit()),
            Node("IsEB", "Entanglement breaking", PositivePredicate(true),
                "Section 8, PDF p. 18: \"For p = 1, we just call the map Φ 𝕂-entanglement breaking.\" Its preceding condition is (Φ ⊗ idᵣ)(P) ∈ SEPₚ(𝕂ᵐ ⊗ 𝕂ʳ) for all positive P and r ≥ 1. The display specializes p to one and adds only the vacuous empty amplification. No trace-preserving or unital condition is imposed.",
                DescribeRole.Definition, Lit()),
            Node("choi", "Input-first Choi matrix", Choi(),
                "The Choi matrix has its input factor first. Applying Phi to the matrix unit Matrix.single a.1 b.1 1 gives its entry at output indices a.2 and b.2. The canonical Kraus Choi matrix places output first; Prod.swap relates the two tensor orders.",
                DescribeRole.Definition, Lit()),
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
            Describe.Remark(DescribeId.Create("flag-lift"), DeclarationHandle.Create(Prefix + "result"),
                H("A composition-compatible flag"), AssessedProvenance.FromRepo(Flags), Blocks(Paragraph(Text(
                    "On the auxiliary two-dimensional factor take P+ = (1,i)(1,i)*/2 and P- = (1,-i)(1,-i)*/2. Their transpose exchanges them. Compress to these flag sectors with B+ and B-, and put E(X) = B+(X) + B-(X)^T and D(A) = A tensor P+ + A^T tensor P-. The lift D Phi E/2 has four completely positive branches for every complex PPT Phi. It is invariant under transpose on input and output, so its real restriction is IPT and complexifies back to the lift. The identity E D = 2 id makes the lift preserve composition. Completely positive insertion A tensor P+ and compression B+ recover Phi squared divided by two. This transfers entanglement breaking from the lifted square. Huber, Lami, Lancien and Müller-Hermes, Lemma III.1, PDF p. 4, supply a tensor-block precedent using X tensor (1-omega) + Y tensor omega; their lemma does not state this two-dimensional map lift.")))),
            Node("result", "The three conjectures are equivalent", Disp(Equivalence()),
                "IPT² over either field in dimension 2n implies PPT² over ℂ in dimension n by the flag lift and recovery. The source's implications PPT²(ℂ) ⇒ IPT²(ℂ) ⇒ IPT²(ℝ) retain dimension n. Entanglement breaking is characterized by a separable input-first Choi matrix, with an explicit tensor swap, and by measure-and-prepare form. Completely positive maps preserve it under pre- and post-composition. The complexification of a real entanglement-breaking map is complex entanglement breaking; in the reverse direction the IPT condition gives CSEP ∩ IPT = real SEP. These facts close both equivalences. The PPT-squared conjecture itself and the possibility of avoiding dimension doubling remain open.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chiribella-davidson-paulsen-rahaman-2023-ppt-ipt-squared-equivalence"),
                    ResolutionKind.Proved)))));

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("ipt-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

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

    private static Formula Amplification()
    {
        Formula a1 = Component("a", 1), a2 = Component("a", 2), b1 = Component("b", 1), b2 = Component("b", 2);
        Formula slice = Fun("i", FinOf(V("n")), Fun("j", FinOf(V("n")), App(V("P"), Pair(V("i"), a2), Pair(V("j"), b2))));
        Formula body = Fun("a", ProdOf(FinOf(V("m")), FinOf(V("r"))),
            Fun("b", ProdOf(FinOf(V("m")), FinOf(V("r"))), App(App(V("Phi"), Parenthesized(slice)), a1, b1)));
        return Disp(Generic(All("Phi", MapOf(V("K")), All("r", N, All("P", TensorMatrix("n", "r"),
            EqTo(Call("ampl", V("Phi"), V("r"), V("P")), body))))));
    }

    private static Formula PositivePredicate(bool breaking)
    {
        Formula image = Call("ampl", V("Phi"), V("r"), V("P"));
        Formula conclusion = breaking ? Member(image, Call("SEP", V("K"), V("m"), V("r"))) : Psd(image);
        Formula body = All("r", N, All("P", TensorMatrix("n", "r"), Imp(Psd(V("P")), conclusion)));
        return Disp(Generic(All("Phi", MapOf(V("K")), IffOf(Call(breaking ? "IsEB" : "IsCP", V("Phi")), body))));
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
        return Disp(Generic(All("Phi", MapOf(V("K")), EqTo(Call("choi", V("Phi")), body))));
    }

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
        Formula choi = Call("choi", V("Phi")), pt = Call("ptFirst", choi);
        Formula body = And(Call("IsCP", V("Phi")), invariant ? EqTo(pt, choi) : Psd(pt));
        return Disp(Generic(All("Phi", MapOf(V("K")), IffOf(Call(invariant ? "IsIPT" : "IsPPT", V("Phi")), body))));
    }

    private static Formula ConjectureBody(Formula scalar, bool invariant) => All("n", N, All("Phi", EndOf(scalar),
        Imp(Call(invariant ? "IsIPT" : "IsPPT", V("Phi")), Call("IsEB", Parenthesized(Square(V("Phi")))))));
    private static Formula ComplexConjecture() => Disp(IffOf(V("PPT2C"), ConjectureBody(C, false)));
    private static Formula IptConjecture() => Disp(All("K", Named("Type"), Instance(IffOf(Call("IPT2", V("K")), ConjectureBody(V("K"), true)))));
    private static Formula Equivalence() => And(IffOf(V("PPT2C"), Call("IPT2", C)), IffOf(Call("IPT2", C), Call("IPT2", R)));
}

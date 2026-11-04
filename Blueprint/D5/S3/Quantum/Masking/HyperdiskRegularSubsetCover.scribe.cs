using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Masking;

internal sealed class HyperdiskRegularSubsetCoverDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/HilbertOperators/dinghu2020masking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A regular subset of a four-dimensional hyperdisk has no finite hyperdisk cover.",
        H("A regular subset without a finite hyperdisk cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-hyperdisk"),
                DeclarationHandle.Create(Module + ".IsHyperdisk"),
                H("Hyperdisks of unit vectors"),
                StatementSource.FromAuthor(Disp(HyperdiskDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A hyperdisk is the full set of unit vectors with specified strictly positive "
                    + "coefficient moduli in a finite orthonormal family spanning its complex linear span. "
                    + "The family has m elements, and r assigns their real coefficient moduli; the span "
                    + "equality makes this family a basis of the displayed span. "
                    + "This is Definition 1 of Ding and Hu, arXiv:1909.11256v3, masking.tex lines 110–125. "
                    + "Pure states are represented by unit vectors, so all global phases remain in the set. "
                    + "The equality of spans and the equality with the entire modulus level set are both required."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-regular-subset"),
                DeclarationHandle.Create(Module + ".IsRegularSubset"),
                H("Regular subsets"),
                StatementSource.FromAuthor(Disp(RegularSubsetDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The set c is regular in s when s is a hyperdisk and intersecting s with the "
                    + "complex linear span of c returns exactly c. The submodule is explicitly "
                    + "coerced to its underlying set before intersection. This is Definition 4, "
                    + "masking.tex lines 251–258; in particular, the equality implies that c is contained in s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The finite-cover question"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The source states: \"A related open question is whether a regular subset of a hyperdisk "
                    + "can be covered with finite number of hyperdisks.\" "
                    + "For every natural dimension n and every regular subset c of a hyperdisk s, "
                    + "the assertion asks for a natural k and k hyperdisks h i, each contained in c, "
                    + "whose union is exactly c. It expresses the second open question in the conclusion, "
                    + "masking.tex line 651, with the contained-cover convention of lines 272–279. "
                    + "There is no positivity restriction on n or k, and no identification of vectors modulo global phase."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A four-coordinate counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "In complex Euclidean four-space, set ρ = (1,2,3,4)/√30 and let S consist "
                        + "of the unit vectors x with |xⱼ| = ρⱼ. Let V be the kernel of the complex "
                        + "coordinate-projection linear map x ↦ 6x₀ + 3x₁ + 2x₂ + 3x₃, and set C = V ∩ S. "
                        + "The squared coordinate moduli sum to one. To see that S spans the whole space, "
                        + "compare the vector with positive real coordinates ρⱼ to the vector obtained "
                        + "by reversing the sign of just coordinate j. Their difference is 2ρⱼ times "
                        + "the jth coordinate vector, and ρⱼ is positive. Thus the standard orthonormal "
                        + "basis exhibits S as a hyperdisk. Since C lies in V, its linear span lies "
                        + "in V as well; hence span(C) ∩ S = C, and C is regular in S.")),
                    Paragraph(Text(
                        "For each natural a take tₐ = −1/2 − 1/(4(a+1)), where a is included in the "
                        + "real numbers. Then −3/4 ≤ tₐ ≤ −1/2. For such a real t put "
                        + "z = t + i√(1−t²), w = −2−z, q = 5+4t and κ = √((4−q)/q). "
                        + "The four complex phases are z, w(1+iκ)/2, w(1−iκ)/2 and 1. "
                        + "Here |z|² = 1, |w|² = q and 0 < q ≤ 4, so the squared moduli of the "
                        + "middle phases are q(1+κ²)/4 = 1. The sum of the first three phases plus "
                        + "twice the fourth is zero. Multiplying these phases coordinatewise by ρ "
                        + "therefore gives a unit vector xₐ in C.")),
                    Paragraph(Text(
                        "If xₐ = u xᵦ for a complex scalar u, comparison of their identical nonzero "
                        + "fourth coordinates gives u = 1. The real parts of the first coordinates "
                        + "then give tₐ = tᵦ. The defining reciprocals have positive denominators, "
                        + "so this equality gives a = b. Thus these vectors lie on pairwise distinct complex rays.")),
                    Paragraph(Text(
                        "The phase comparison used next starts with complex A and B. If "
                        + "|−A+B| = |A+B| and |iA+B| = |A+B|, expanding the squared moduli makes "
                        + "both the real and imaginary parts of A times the conjugate of B zero. "
                        + "Consequently A = 0 or B = 0. Now suppose the modulus of a finite sum "
                        + "of coefficients times independent unit phases is constant. If one coefficient "
                        + "is nonzero, varying its phase through 1, −1 and i forces the sum of all "
                        + "remaining terms to vanish for every choice of their phases. Comparing the "
                        + "all-one choice with the choice that negates a second phase makes that "
                        + "second coefficient zero. Hence at most one coefficient is nonzero.")),
                    Paragraph(Text(
                        "For an orthonormal system φ spanning a vector x, orthonormal expansion "
                        + "reconstructs x from its inner-product coefficients. The orthogonal-family "
                        + "norm identity gives the squared norm of a linear combination of the φ p "
                        + "as the sum of the squared coefficient "
                        + "moduli. Therefore, if x belongs to a hyperdisk with positive coefficient "
                        + "moduli r p, those moduli have squared sum one, and every vector "
                        + "Σₚ (r p)uₚ φ p with independent unit phases uₚ belongs to the same hyperdisk; "
                        + "the real numbers r p are included in the complex scalars. If this hyperdisk "
                        + "is contained in C, each coordinate of these vectors has the constant modulus "
                        + "ρⱼ. Applying the phase comparison coordinate by coordinate shows that "
                        + "distinct vectors φ p have disjoint coordinate supports.")),
                    Paragraph(Text(
                        "The cancellation obstruction concerns two disjointly supported "
                        + "four-coordinate vectors whose coordinate sums are zero. Suppose the first "
                        + "has fourth-coordinate modulus 2 and each of its first three coordinates "
                        + "is zero or has modulus 1. Its fourth coordinate forces the second vector's "
                        + "fourth coordinate to vanish. The first vector cannot have zero or just "
                        + "one nonzero coordinate among its first three: their sum could not cancel "
                        + "a term of modulus 2. If it has exactly two, the second vector can only "
                        + "have the remaining coordinate, which its zero-sum condition forces to vanish. "
                        + "If it has all three, disjointness already makes the second vector zero.")),
                    Paragraph(Text(
                        "Also, if a linear combination of independent unit phases vanishes for "
                        + "every phase choice, comparing all phases equal to one with one phase "
                        + "negated shows that each coefficient vanishes. Apply this to the functional "
                        + "defining V and to all phase choices in a hyperdisk contained in C. "
                        + "It follows that every φ p separately lies in V. For each p, multiply the "
                        + "jth coordinate of (r p)φ p by the jth entry of (6,3,2,3) and by √30/6. "
                        + "The resulting vector has coordinate sum zero; on its nonzero coordinates "
                        + "its moduli are the corresponding entries of (1,1,1,2). Indeed the vector "
                        + "with all phases equal to one belongs to C, and disjoint supports isolate "
                        + "each nonzero coordinate. Its fourth coordinate is nonzero, so some φ p "
                        + "has a nonzero fourth coordinate. The cancellation obstruction forces every "
                        + "other scaled vector to vanish. That would make every other φ p zero, "
                        + "contradicting orthonormality. Thus there is at most one basis vector.")),
                    Paragraph(Text(
                        "A hyperdisk contained in C and containing a unit vector cannot have an "
                        + "empty basis, since orthonormal reconstruction would make that vector zero. "
                        + "It therefore has exactly one basis vector. Expanding any two of its "
                        + "vectors x and y in that basis shows that x is the scalar multiple of y "
                        + "given by the ratio of their inner-product coefficients; the denominator "
                        + "is nonzero because its modulus is strictly positive. Hence any two vectors "
                        + "in such a hyperdisk lie on the same complex ray. The proof uses that a "
                        + "nonempty Fin m with m ≤ 1 is subsingleton, so the single surviving basis "
                        + "index supports the reconstruction.")),
                    Paragraph(Text(
                        "Assume a finite cover of C by hyperdisks h i indexed by Fin k. For each "
                        + "natural a choose f(a) with xₐ in h(f(a)). If f(a) = f(b), the preceding "
                        + "one-ray conclusion makes xₐ a complex scalar multiple of xᵦ, so a = b. "
                        + "This gives an injection from the natural numbers into Fin k, which would "
                        + "make the natural numbers finite. Their infinitude is the contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ding-hu-2020-hyperdisk-regular-subset-finite-cover"),
                    ResolutionKind.Refuted)))));

    private static Formula HyperdiskDefinition()
    {
        Formula spanEquality = Equal(
            Span(At(Qualified("Set", "range"), X("φ"))), Span(X("s")));
        Formula positive = All("j", FinOf(X("m")),
            Less(Typed(D(0), Reals()), At(X("r"), X("j"))));
        Formula coefficient = Equal(new Formula.Norm(
            At(Qualified("inner"), Complexes(), At(X("φ"), X("j")), X("ψ"))),
            At(X("r"), X("j")));
        Formula levelSet = Seq(OpenBrace, Typed(X("ψ"), Space()), Sp, Mid, Sp,
            Conjunction(Equal(new Formula.Norm(X("ψ")), Typed(D(1), Reals())),
                All("j", FinOf(X("m")), coefficient)), CloseBrace);
        Formula data = Some("m", Naturals(),
            Some("φ", Arrow(FinOf(X("m")), Space()),
                Some("r", Arrow(FinOf(X("m")), Reals()),
                    Conjunction(At(Qualified("Orthonormal"), Complexes(), X("φ")),
                        Conjunction(spanEquality, Conjunction(positive, Equal(X("s"), levelSet)))))));
        return All("n", Naturals(), All("s", StateSet(),
            Equal(LocalCall("IsHyperdisk", X("s")), Parenthesized(data))));
    }

    private static Formula RegularSubsetDefinition() => All("n", Naturals(),
        All("c", StateSet(), All("s", StateSet(),
            Equal(LocalCall("IsRegularSubset", X("c"), X("s")),
                Parenthesized(Conjunction(LocalCall("IsHyperdisk", X("s")),
                    Equal(At(Qualified("Set", "inter"),
                        Typed(At(Qualified("SetLike", "coe"), Span(X("c"))), StateSet()),
                        X("s")), X("c"))))))));

    private static Formula ClaimProposition()
    {
        Formula members = All("i", FinOf(X("k")),
            Conjunction(LocalCall("IsHyperdisk", At(X("h"), X("i"))),
                new Formula.Relation(At(X("h"), X("i")),
                    FormulaRelationOperator.SubsetOf, X("c"))));
        Formula union = At(Qualified("Set", "iUnion"),
            LambdaOf("i", FinOf(X("k")), At(X("h"), X("i"))));
        Formula cover = Some("k", Naturals(), Some("h", Arrow(FinOf(X("k")), StateSet()),
            Conjunction(members, Equal(X("c"), union))));
        return All("n", Naturals(), All("s", StateSet(), All("c", StateSet(),
            Arrow(LocalCall("IsRegularSubset", X("c"), X("s")), cover))));
    }

    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Masking", "HyperdiskRegularSubsetCover", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula X(string name) => name switch
    {
        "φ" => Phi,
        "ψ" => Psi,
        _ => F.Id(name),
    };
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Space() => At(Qualified("EuclideanSpace"), Complexes(), FinOf(X("n")));
    private static Formula StateSet() => At(Qualified("Set"), Space());
    private static Formula Span(Formula set) => At(Qualified("Submodule", "span"), Complexes(), set);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums.Fermat;

internal sealed class CharacterPointCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CharacterSums/Fermat/CharacterPointCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplicative characters count actual affine and projective Fermat points over every finite field, with the zero-fiber correction and the Weil error bound.",
        H("Fermat Point Counts from Multiplicative Characters"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fermat-character-kernel-power-image"),
                DeclarationHandle.Create(Prefix + "character_kernel_eq_power_image"),
                H("Character kernel is the power image"),
                StatementSource.FromAuthor(KernelStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let F be a finite field and let chi be a complex multiplicative character of exact order d. "
                    + "Evaluation on a generator of the cyclic unit group embeds the character group into the complex units. "
                    + "The value of chi on that generator has order d, so its kernel consists exactly of d-th powers. "
                    + "This supplies the existence part of the root-count identity below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fermat-power-root-count"),
                DeclarationHandle.Create(Prefix + "power_fiber_card_eq_character_sum"),
                H("Root counting includes the zero fiber"),
                StatementSource.FromAuthor(RootStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume d is positive. A nonzero d-th power has d roots because every nonempty power fiber "
                    + "is equivalent to the kernel of the power homomorphism. Non-powers have no roots, and zero has exactly one root. "
                    + "A finite geometric sum of character powers recovers the nonzero count. Mathlib extends even the trivial "
                    + "multiplicative character by zero at zero, so the separate delta term is essential. "
                    + "The equivalent one-plus-nontrivial-characters form is used on the live path to affine counting."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fermat-affine-point-count"),
                DeclarationHandle.Create(Prefix + "affine_point_count"),
                H("Affine Fermat points are a double Jacobi sum"),
                StatementSource.FromAuthor(AffineStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The affine carrier is the actual subtype of pairs satisfying x^d + y^d = 1. The Jacobi sum is J(alpha,beta) = sum over t in F of alpha(t) beta(1-t). "
                    + "Record t = x^d to obtain a genuine equivalence with the sum of two-root fibers. "
                    + "Insert the root-count identity and expand. Both linear terms vanish by nontrivial-character orthogonality, "
                    + "including after the bijection t maps to 1-t. The remaining mixed terms are exactly the Jacobi sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fermat-projective-chart-count"),
                DeclarationHandle.Create(Prefix + "projective_card_eq_affine_add_infinity"),
                H("Actual projective points split into two charts"),
                StatementSource.FromAuthor(ChartStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Projective points are a subtype of Mathlib's projectivization of the three-dimensional coordinate space. "
                    + "The equation is homogeneous, so membership is independent of the chosen representative. "
                    + "A point with nonzero last coordinate normalizes uniquely to [x:y:1]. At infinity, the equation and "
                    + "nonzero representative force the middle coordinate to be nonzero, giving the unique form [t:1:0] "
                    + "with t^d + 1 = 0. The proof constructs a bijection from these two charts to the genuine projective subtype. "
                    + "The hypothesis d is nonzero is required at infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fermat-projective-point-count"),
                DeclarationHandle.Create(Prefix + "projective_point_count"),
                H("The infinity chart cancels the inverse-character pairs"),
                StatementSource.FromAuthor(ProjectiveStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The infinity count is the root count at -1. For each nontrivial exponent i, the exponent d-i "
                    + "gives the inverse character, and its Jacobi sum equals minus chi^i(-1). These terms cancel the "
                    + "nonconstant infinity contribution. The remaining sum omits exactly one term from each row. "
                    + "This statement counts actual projective points and applies also in characteristic two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fermat-projective-weil-bound"),
                DeclarationHandle.Create(Prefix + "projective_weil_bound"),
                H("Weil error for the Fermat point count"),
                StatementSource.FromAuthor(BoundStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume d is at least two and divides Q-1. The proof constructs a complex multiplicative character of exact order d from a primitive complex d-th root of unity. "
                        + "Both characters and their product are nontrivial for every remaining pair. "
                        + "The standard Jacobi-sum product identity with the inverse characters, together with complex conjugation, "
                        + "gives norm sqrt(Q). There are exactly (d-1)(d-2) remaining pairs. The triangle inequality "
                        + "and the bound of the real part by the complex norm give the claimed error for Q = card(F).")),
                    Paragraph(Text(
                        "These are classical finite-field character-sum results, with no mathematical novelty claim. "
                        + "The library contribution connects unit-group characters and Jacobi sums to the actual affine and projective "
                        + "carriers and their cardinalities. The exact identities take an exact-order character as input, while the final bound constructs it from divisibility.")),
                    Paragraph(Text(
                        "For d = 3 the remaining exponent pairs are (1,1) and (2,2), and their Jacobi sums are complex conjugates. "
                        + "Thus the formula gives Q + 1 + 2 Re J(chi,chi) and an error at most 2 sqrt(Q). "
                        + "CubicJacobiNormalization proves J(chi,chi) = -pi for the Euler character at the specified Eisenstein prime. "
                        + "CubicFermatTrace transports that same character through a concrete complex embedding to obtain "
                        + "q + 1 - Tr(pi) for actual projective points over finite Eisenstein residue fields. "
                        + "The prime-period theory retains its rational-prime data; other finite-field extensions require a separate Jacobi normalization theorem."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("The split-prime trace on the congruent-number curve"), Blocks(
                Paragraph(Text("Let p be prime with p congruent to 1 modulo 4, and let a and b be integers with "
                    + "p=a²+b², a odd and b even. Over F=ZMod p use the Weierstrass coefficients (0,0,0,-1,0), "
                    + "so the equation is y²=x³-x. Its discriminant is 64, a unit since p is odd. The actual "
                    + "carrier W.toAffine.Point is equivalent to the option type of the affine solution fibers: "
                    + "none is the unique point at infinity and each remaining point has coordinates x and y "
                    + "with y²=x³-x. Write N for the cardinality of that carrier and T=p+1-N. For each x the "
                    + "number of roots is 1+φ(x³-x), where φ is the quadratic character with φ(0)=0. Counting "
                    + "the fibers and the one point at infinity gives T=-∑ₓ φ(x³-x) in the integers.")),
                Paragraph(Text("Since 4 divides p-1, choose a complex character χ of order four using the "
                    + "primitive fourth root i. Compare the two formulas for the cardinality of each square "
                    + "fiber, using "),
                    Ref(Prefix + "power_fiber_card_eq_one_add_character_sum"),
                    Text(" at order two and Mathlib's quadratic root count. They identify χ² with the complex "
                    + "image of φ at every field element. Also φ(-1)=1. Multiplicativity rewrites "
                    + "φ(x³-x) as χ(x²)φ(x²-1). Reindex the finite sum by t=x² and insert its fiber "
                    + "multiplicity 1+φ(t). Since φ(t-1)=φ(1-t) and χφ=χ⁻¹, the sum becomes "
                    + "J(χ,φ)+J(χ⁻¹,φ). These are complex conjugates because φ is its own inverse.")),
                Paragraph(Text("The quartic Jacobi congruence gives J=J(χ,φ)=-1+z(i-1)² with z in the image "
                    + "of the Gaussian integers. For z=r+si the Gaussian lift j of J has coordinates "
                    + "(-1+2s,-2r), so the real coordinate is odd and the imaginary coordinate even. "
                    + "The three characters χ, φ, and χφ are nontrivial; "),
                    Ref(Prefix + "norm_jacobiSum"),
                    Text(" gives |J|=√p, hence the Gaussian norm of j is p. The trace is T=-2 Re(J).")),
                Paragraph(Text("Write w=a+bi. The norm identities give j times its conjugate equal to w "
                    + "times its conjugate, both equal to p. A Gaussian integer of norm p is irreducible "
                    + "by multiplicativity of the norm and reflection of units, and hence prime in the "
                    + "Gaussian Euclidean domain. Thus j divides w or its conjugate, and the divisible "
                    + "factor is associated to j. By "),
                    Ref("D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.gaussian_unit"),
                    Text(", the unit relating them is one of 1,i,-1,-i. The units ±i would make the "
                    + "real coordinate even, contrary to the oddness of a, so |Re(J)|=|a|. This gives "
                    + "|T|=2|a|. For c=T/(2√p), positivity of √p and p=a²+b² now give "
                    + "|c|=|a|/√p=|a|/√(a²+b²) in the reals.")),
                Paragraph(Text("This is Gauss's classical split-prime calculation. It applies to every "
                    + "prime and representation with the stated congruence and parity, without choosing "
                    + "a sign for the trace. The calculation gives no inert-prime formula, general Hasse "
                    + "bound, or Sato–Tate distribution.")))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parameters() => F.Seq(
        Forall, Sp, F.Id("F"), Comma, Sp, Call("FiniteField", F.Id("F")), Comma, Sp,
        Forall, Sp, F.Id("chi"), Colon, Sp, Call("MulChar", F.Id("F"), F.Id("C")), Comma, Sp,
        Forall, Sp, F.Id("d"), Colon, Sp, F.Id("N"), Comma, Sp,
        Call("orderOf", F.Id("chi")), Eq, F.Id("d"), Sp, Implies, Sp);
    private static Formula PositiveParameters() => F.Seq(Parameters(),
        D(0), Lt, F.Id("d"), Sp, Implies, Sp);
    private static Formula KernelStatement() => Disp(F.Seq(Parameters(),
        Call("ker", Call("toUnitHom", F.Id("chi"))), Eq,
        Call("range", Call("powerHom", F.Id("d")))));
    private static Formula RootStatement() => Disp(F.Seq(PositiveParameters(),
        Forall, Sp, F.Id("a"), Colon, Sp, F.Id("F"), Comma, Sp,
        Call("card", Call("powerFiber", F.Id("a"), F.Id("d"))), Eq,
        Call("deltaZero", F.Id("a")), Plus,
        F.Seq(Sum, Underscore, Grp(D(0), Leq, Sp, F.Id("i"), Lt, F.Id("d")), Sp,
            Call("apply", Call("pow", F.Id("chi"), F.Id("i")), F.Id("a")))));
    private static Formula JacobiPairSum(bool omitInverse) => F.Seq(
        Sum, Underscore, Grp(D(1), Leq, Sp, F.Id("i"), Lt, F.Id("d")), Sp,
        Sum, Underscore, omitInverse
            ? Grp(D(1), Leq, Sp, F.Id("j"), Lt, F.Id("d"), Comma, Sp,
                F.Id("j"), Neq, Sp, F.Id("d"), Minus, F.Id("i"))
            : Grp(D(1), Leq, Sp, F.Id("j"), Lt, F.Id("d")), Sp,
        Call("J", Call("pow", F.Id("chi"), F.Id("i")),
            Call("pow", F.Id("chi"), F.Id("j"))));
    private static Formula AffineStatement() => Disp(F.Seq(PositiveParameters(),
        Call("card", Call("affinePoints", F.Id("F"), F.Id("d"))), Eq,
        Call("card", F.Id("F")), Plus, JacobiPairSum(false)));
    private static Formula ChartStatement() => Disp(F.Seq(
        Forall, Sp, F.Id("F"), Comma, Sp, Call("FiniteField", F.Id("F")), Comma, Sp,
        Forall, Sp, F.Id("d"), Colon, Sp, F.Id("N"), Comma, Sp, F.Id("d"), Neq, D(0), Sp, Implies, Sp,
        Call("card", Call("projectivePoints", F.Id("F"), F.Id("d"))), Eq,
        Call("card", Call("affinePoints", F.Id("F"), F.Id("d"))), Plus,
        Call("card", Call("infinityPoints", F.Id("F"), F.Id("d")))));
    private static Formula ProjectiveStatement() => Disp(F.Seq(PositiveParameters(),
        Call("card", Call("projectivePoints", F.Id("F"), F.Id("d"))), Eq,
        Call("card", F.Id("F")), Plus, D(1), Plus,
        JacobiPairSum(true)));
    private static Formula BoundStatement() => Disp(F.Seq(
        Forall, Sp, F.Id("F"), Comma, Sp, Call("FiniteField", F.Id("F")), Comma, Sp,
        Forall, Sp, F.Id("d"), Colon, Sp, F.Id("N"), Comma, Sp,
        D(2), Leq, Sp, F.Id("d"), Comma, Sp,
        Call("divides", F.Id("d"), F.Seq(Call("card", F.Id("F")), Minus, D(1))),
        Sp, Implies, Sp,
        new Formula.Norm(F.Seq(Call("card", Call("projectivePoints", F.Id("F"), F.Id("d"))), Minus,
            F.Open, Call("card", F.Id("F")), Plus, D(1), F.Close)), Leq,
        F.Open, F.Id("d"), Minus, D(1), F.Close,
        F.Open, F.Id("d"), Minus, D(2), F.Close,
        Call("sqrt", Call("card", F.Id("F")))));
}

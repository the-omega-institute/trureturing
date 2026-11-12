using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating unit polygon has exactly m minus two distinct pairs of nonzero real eigenvalues.",
        H("Alternating vortex polygon spectrum"), Blocks(
            Node("charge", "Alternating charge", ChargeFormula(),
                "The zero-based label j represents the source's label j+1, so its charge is minus one to the power j.val+2. "
                    + "This is the alternating pattern of Section 4.1, arXiv:1306.1545v2, TeX lines 506–507.",
                AssessedProvenance.FromLiterature(Source)),
            Node("field", "The Cartesian point-vortex field", FieldFormula(),
                "The two summands of Fin N ⊕ Fin N label the x and y coordinates. The field is Equations (1)–(2) "
                    + "with b=2 and Ω=1/2 (TeX lines 168–176 and 526–532). Self-interactions are set to zero. "
                    + "Real division defines a total function, while at distinct polygon vertices all interaction denominators are nonzero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("polygon", "The regular unit polygon", PolygonFormula(),
                "The coordinates are the cosine and sine of 2π(j.val+1)/N. This is the source's order "
                    + "z₁=exp(2πi/N), through zN=1 (TeX line 515). The source sets Ω=1/2 for the even polygon equilibrium (TeX lines 524–532).",
                AssessedProvenance.FromLiterature(Source)),
            Node("jacobian", "The Cartesian linearization", JacobianFormula(),
                "The entry in row p and column q is the derivative at zero of the pth field coordinate along the affine line "
                    + "through the polygon in direction Pi.single q 1. It is the Cartesian Jacobian of the source's model; "
                    + "the source examines its linearization in polar coordinates (TeX lines 543–550).",
                AssessedProvenance.FromLiterature(Source)),
            Supplier("chord_sq", "The actual polygon distances",
                "The canonical chord identity is exposed for collision-free parameter transport; its proof is reused unchanged.", DescribeRole.Theorem),
            Supplier("chord_sq_ne_zero", "Collision-free polygon vertices",
                "Every pair of distinct labels has nonzero squared distance. This is the domain certificate used by the differentiated Cartesian field.", DescribeRole.Theorem),
            Supplier("equilibrium_all", "Equilibrium including the small polygons",
                "The existing Cartesian reflection proof applies for every m at least one. The earlier m at least three supplier remains a consumer of this proof body.", DescribeRole.Theorem),
            Supplier("rotation", "Radial and tangential coordinates",
                "The columns at vertex j are (xj,yj) and (-yj,xj). The source note uses a uniformly rotated polygon, so this explicit Cartesian rotation fixes the correspondence.", DescribeRole.Definition),
            Supplier("rotation_mul_transpose", "The coordinate rotation is orthogonal",
                "The canonical proof uses xj squared plus yj squared equal to one. No presumed spectral decomposition is involved.", DescribeRole.Theorem),
            Supplier("rotated_jacobian_all", "Actual block derivative for every even polygon",
                "The existing derivative and rotation proof gives the off-diagonal blocks B and C for every m at least one, including the dipole and square.", DescribeRole.Theorem),
            Supplier("nonzero_characteristic_value", "Schur determinant equality",
                "The canonical Schur proof yields an equality of evaluations for each nonzero real argument, strengthening its earlier root-test consumer without repeating the determinant foundation.", DescribeRole.Theorem),
            Supplier("charpoly_mode_product", "Complete characteristic polynomial",
                "A polynomial equality follows because the Schur equality and canonical block-product spectrum agree at infinitely many nonzero real arguments. The identity therefore also includes zero.", DescribeRole.Theorem),
            Supplier("complex_charpoly_mode_product", "The actual complexified characteristic polynomial",
                "Map the polynomial identity through the real inclusion into the complex numbers. This concerns the characteristic polynomial of the actual Cartesian Jacobian, and includes every complex root; it does not by itself prove geometric multiplicities or Jordan structure.", DescribeRole.Theorem),
            Node("claim", "The distinct-real-pair conjecture", Equal(Local("claim"), Parenthesized(ClaimProposition())),
                "Conjecture 4.4 asks for N/2−2 distinct pairs of real eigenvalues of the alternating N-gon (TeX lines 627–633). "
                    + "For N=2m and m≥3, this proposition asserts sign symmetry of every real characteristic root and "
                    + "cardinality 2(m−2) for the set of nonzero real roots. Zero and algebraic multiplicities are excluded from the count. "
                    + "The source proposes this assertion as a conjecture.", AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Exactly m minus two real pairs"),
                StatementSource.FromAuthor(Disp(ClaimProposition())), AssessedProvenance.FromRepo(Source),
                Proof(), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barry-kevrekidis-2013-alternating-vortex-polygon-spectrum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Supplier(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static BlockSequence Proof() => Blocks(
        Paragraph(Text(
            "First prove distinctness of the prospective squared positive roots. For natural numbers 2≤k<l<m, "
                + "put s=k+l and f(a)=(m−a)²(a²−2), using real arithmetic. Then f(k)−f(l)=(k−l)Q(m), "
                + "where Q(t)=st²−2(k²+kl+l²−2)t+s(k²+l²−2). One has Q(l)=−(l−k)(k²−2)<0. "
                + "Writing u=k−2 and v=l−k−1 gives Q(s−1)=−(2u²+2uv+4u+v+1)<0. "
                + "If m<s, use (k−1)Q(m)=(s−1−m)Q(l)+(m−l)Q(s−1)−s(k−1)(m−l)(s−1−m)<0. "
                + "If m≥s, put h=m−s≥0; then Q(m)=2s+(2kl+4)h+sh²>0. Thus Q(m)≠0 and f(k)≠f(l).")),
        Paragraph(Text(
            "The squared distance between polygon vertices j and k is 4sin²(π(j.val−k.val)/N). For j≠k the angle "
                + "lies strictly between −π and π and is nonzero, so this distance is nonzero. Differentiate the field "
                + "along z(t)=polygon N+t·Pi.single q 1, using the quotient rule and finite-sum differentiation. "
                + "For a squared distance d and its directional derivative e, each quotient derivative has numerator "
                + "equal to the directional coordinate difference times d minus the coordinate difference times e, "
                + "and denominator d². The self-interaction derivative is zero.")),
        Paragraph(Text(
            "For N=2m the reflection k↦j+j−k preserves the alternating charge. For either Cartesian coordinate v, "
                + "the two reflected terms (v(j)−v(k))/d(j,k) and (v(j)−v(j+j−k))/d(j,j+j−k) sum to v(j). "
                + "The total alternating charge is zero, so the interaction sum equals −charge N j·v(j)/2. "
                + "This cancels the precession term in each field coordinate, proving that the polygon is an equilibrium.")),
        Paragraph(Text(
            "At vertex j use the radial and tangential columns (xj,yj) and (−yj,xj). The resulting matrix has blocks "
                + "diag(x), −diag(y), diag(y), diag(x), and its product with its transpose is the identity by xj²+yj²=1. "
                + "Conjugating the differentiated Cartesian matrix by it gives zero diagonal blocks. At distinct vertices "
                + "both off-diagonal block entries are −charge N k·weights m j k. On the diagonal the upper-right entry "
                + "is w=Σk charge N k·weights m j k and the lower-left entry is charge N j+w; the equilibrium identities "
                + "give these simplifications. The alternating weight sum yields w=charge N j·diagonalWeight m. "
                + "Thus the four blocks are 0, blockB m, blockC m, 0.")),
        Paragraph(Text(
            "For nonzero real x, similarity preserves the characteristic polynomial. Apply the Schur determinant formula "
                + "to xI, −blockB m, −blockC m, xI, using the inverse x⁻¹I of xI. Scale the Schur complement by x "
                + "and cancel nonzero determinants. Then x is a characteristic root exactly when "
                + "det(x²I−blockC m·blockB m)=0. The product_spectrum identity factors this determinant into "
                + "the product of x²−gamma m k over k in ZMod (2m). Its common Fourier basis uses the inverse-squared-chord "
                + "Fourier values and the shift by m induced by alternating signs.")),
        Paragraph(Text(
            "For a vanishing factor put r=min(k.val,2m−k.val), so 0≤r≤m and x²=(m−r)²(r²−2)/4. "
                + "Since x≠0, its square is positive. The cases r=0 and r=1 make the right side nonpositive, "
                + "and r=m makes it zero. Therefore 2≤r<m. Conversely, every natural r in this interval gives "
                + "a residue with least representative r and hence this factor. The nonzero real roots are exactly "
                + "±(m−r)√(r²−2)/2 for 2≤r<m.")),
        Paragraph(Text(
            "The positive expression is strictly positive and has the required square. The initial argument makes its "
                + "values distinct for distinct r. Negation is injective, and its image is disjoint from the positive image. "
                + "The natural interval from 2 to m−1 has m−2 elements, so the union has 2(m−2) elements. "
                + "The determinant condition depends only on x², giving sign symmetry for nonzero roots; zero is fixed by negation. "
                + "Both conclusions hold for every m≥3.")),
        Paragraph(Text(
            "This concerns the point-vortex field with b=2, Ω=1/2 and unit radius. It asserts no odd-polygon, "
                + "other-charge, eigenvector, nonlinear-stability or Gross–Pitaevskii stability conclusion.")));

    private static Formula ChargeFormula() => All("N", Naturals(), All("j", FinOf(X("N")),
        Equal(LocalCall("charge", X("N"), X("j")), Power(Negate(Typed(D(1), Reals())), Add(Val(X("j")), D(2))))));

    private static Formula FieldFormula()
    {
        Formula j = X("j"), k = X("k"), z = X("z"), size = X("N");
        Formula Coordinate(string side, Formula index) => At(z, At(Qualified("Sum", side), index));
        Formula dx = Subtract(Coordinate("inl", j), Coordinate("inl", k));
        Formula dy = Subtract(Coordinate("inr", j), Coordinate("inr", k));
        Formula denominator = Add(Power(dx, D(2)), Power(dy, D(2)));
        Formula Interaction(Formula difference) => SumOver("k", FinOf(size), If(Equal(k, j), Typed(D(0), Reals()),
            Divide(Multiply(LocalCall("charge", size, k), difference), denominator)));
        Formula precession = Multiply(LocalCall("charge", size, j), Divide(Typed(D(1), Reals()), D(2)));
        Formula first = Subtract(Multiply(Multiply(Negate(LocalCall("charge", size, j)),
            Divide(Typed(D(1), Reals()), D(2))), Coordinate("inr", j)), Interaction(dy));
        Formula second = Add(Multiply(precession, Coordinate("inl", j)), Interaction(dx));
        Formula value = At(Qualified("Sum", "elim"), LambdaOf("j", FinOf(size), first), LambdaOf("j", FinOf(size), second), X("p"));
        return All("N", Naturals(), All("z", Arrow(Index(size), Reals()),
            Equal(LocalCall("field", size, z), LambdaOf("p", Index(size), value))));
    }

    private static Formula PolygonFormula()
    {
        Formula size = X("N");
        Formula angle = Divide(Multiply(Multiply(D(2), Qualified("Real", "pi")), Add(CastReal(Val(X("j"))), D(1))), CastReal(size));
        Formula value = At(Qualified("Sum", "elim"),
            LambdaOf("j", FinOf(size), At(Qualified("Real", "cos"), angle)),
            LambdaOf("j", FinOf(size), At(Qualified("Real", "sin"), angle)), X("p"));
        return All("N", Naturals(), Equal(LocalCall("polygon", size), LambdaOf("p", Index(size), value)));
    }

    private static Formula JacobianFormula()
    {
        Formula size = X("N");
        Formula line = Add(LocalCall("polygon", size), Smul(X("t"), At(Qualified("Pi", "single"), X("q"), Typed(D(1), Reals()))));
        Formula derivative = At(Qualified("deriv"), LambdaOf("t", Reals(), LocalCall("field", size, line, X("p"))), Typed(D(0), Reals()));
        return All("N", Naturals(), All("p", Index(size), All("q", Index(size), Equal(LocalCall("jacobian", size, X("p"), X("q")), derivative))));
    }

    private static Formula ClaimProposition()
    {
        Formula matrix = LocalCall("jacobian", Multiply(D(2), X("m")));
        Formula Root(Formula value) => At(Qualified("Polynomial", "IsRoot"), At(Qualified("Matrix", "charpoly"), matrix), value);
        Formula symmetry = All("x", Reals(), Implication(Root(X("x")), Root(Negate(X("x")))));
        Formula roots = Seq(OpenBrace, Typed(X("x"), Reals()), Sp, Mid, Sp,
            Conjunction(NotEqual(X("x"), Typed(D(0), Reals())), Root(X("x"))), CloseBrace);
        Formula count = Equal(At(Qualified("Set", "ncard"), roots), Multiply(D(2), Typed(Subtract(X("m"), D(2)), Naturals())));
        return All("m", Naturals(), Implication(LE(D(3), X("m")), Conjunction(symmetry, count)));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Local(string name) => Qualified("D5", "S3", "FluidDynamics", "Vortices", "AlternatingPolygonSpectrum", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Index(Formula size) => At(Qualified("Sum"), FinOf(size), FinOf(size));
    private static Formula Val(Formula value) => At(Qualified("Fin", "val"), value);

    private static Formula X(string name) => F.Id(name);
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula CastReal(Formula value) => Typed(value, Reals());
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Divide(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
}

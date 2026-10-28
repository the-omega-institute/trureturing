using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class WronskianPerfectLonelyAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/LieTheory/keninskiselev2026wronskianalgebras");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A perfect homogeneous one-generator polynomial extension exists exactly at differential order one.",
        H("Perfect polynomial extensions for complete Wronskians"),
        Blocks(
            Definition("multi-index-set", "I", "The differential multi-indices", IndexFormula(),
                "I d k is the finite set of all finitely supported natural-valued multi-indices on Fin d "
                    + "whose total degree is at most k. Each index occurs once. These are the derivative "
                    + "indices in the source's complete Wronskian (TeX lines 613–630)."),
            Definition("pderiv-multi", "pderivMulti", "Iterated partial differentiation", PartialFormula(),
                "For a multi-index α, take the α i-th power of the linear map underlying the partial "
                    + "derivative in coordinate i, and multiply these endomorphisms along List.finRange d. "
                    + "Multiplication is composition, and the empty product is the identity. This is "
                    + "ordinary repeated partial differentiation, with no divided-power normalization "
                    + "(source, TeX lines 616–620). The definition applies over any field K."),
            Definition("wronskian", "wronskian", "The complete generalized Wronskian", WronskianFormula(),
                "The rows are indexed by the differential multi-indices and the columns by the polynomial "
                    + "arguments f β. The entry in row α and column β is the α-th iterated partial derivative "
                    + "of f β. Its determinant is the complete generalized Wronskian of differential order k "
                    + "(source, TeX lines 625–630), expressed for polynomials over any field K. "
                    + "The index type is displayed as the subtype of multi-indices belonging to I d k; "
                    + "Subtype.val extracts a row's multi-index, and DFunLike.coe applies its linear map."),
            Definition("lonely", "lonely", "The one-generator polynomial extension", LonelyFormula(),
                "The subspace lonely p is the sum of the polynomials of total degree at most k and "
                    + "the line through p. The supremum is the sum of these submodules, and the line "
                    + "is the span of the singleton containing p. When p is nonzero and homogeneous of "
                    + "degree k + 1, this is the direct sum in the source's question (TeX lines 1258–1260). "
                    + "The definition itself requires neither homogeneity nor nonzeroness."),
            Definition("perfect", "perfect", "Perfectness of the extension", PerfectFormula(),
                "Perfectness means that the K-linear span of every Wronskian whose arguments lie in "
                    + "lonely p equals lonely p itself (source, TeX lines 517–521). This equality includes "
                    + "closure under the bracket as well as generation by bracket values. The definition "
                    + "does not require a nonzero or homogeneous p."),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Existence exactly at differential order one"),
                StatementSource.FromAuthor(Disp(IffOf(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Over every characteristic-zero field K, for every d at least two and k at least one, "
                        + "there is a nonzero homogeneous polynomial p of degree k + 1 with a perfect "
                        + "extension if and only if k equals one. This answers the existence question "
                        + "of TeX lines 1258–1260 with a characterization of the possible orders, and "
                        + "includes both real and complex coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The order obstruction and the quadratic construction"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Start with the generating family consisting of p and the monomials x^α for α in I d k. "
                            + "Expand every argument of a Wronskian in this family. Multilinearity expresses "
                            + "every bracket as a linear combination of brackets of generators.")),
                    Paragraph(Text(
                        "Iterated differentiation lowers integer-valued homogeneous degree by the order "
                            + "of differentiation. In each determinant term every row is used once, so for "
                            + "homogeneous arguments of degrees n β the bracket is homogeneous of degree "
                            + "the sum of n β minus the sum of the row degrees, with natural subtraction "
                            + "in the nonnegative formulation. This follows by first computing degrees "
                            + "with integer weights and then returning to natural degrees. If p is "
                            + "homogeneous of degree k + 1, a bracket containing every generator except "
                            + "p has degree zero, while omitting "
                            + "x^α gives degree k + 1 minus the degree of α.")),
                    Paragraph(Text(
                        "A repeated generator gives two equal columns and determinant zero. An injective "
                            + "choice of generators omits exactly one member of the family and differs from "
                            + "the bracket that omits that member only by the sign of a column permutation. "
                            + "Thus the generator brackets all lie in the span of brackets obtained by omitting one generator. "
                            + "Suppose k is at least two. Project onto the homogeneous component of degree k. "
                            + "All these brackets vanish under this projection except the d brackets "
                            + "omitting a degree-one monomial. The projection of every bracket, and hence "
                            + "of their span, lies in a subspace s generated by these d polynomials. "
                            + "Perfectness would put the degree-k component of every element of lonely p "
                            + "in s. Choose the two distinct coordinates i₀ = 0 and i₁ = 1. "
                            + "The d pure powers x_i^k together with x_i₀^(k−1)x_i₁ are d + 1 distinct "
                            + "degree-k monomials. They belong to lonely p, are fixed by the projection, "
                            + "and are linearly independent. Thus d + 1 is at most the dimension of s, "
                            + "whereas its d generators give dimension at most d. This contradiction "
                            + "excludes perfectness for every homogeneous p when k is at least two.")),
                    Paragraph(Text(
                        "For order one, the differential indices are zero and the single-coordinate "
                            + "unit multi-indices. Their operators are respectively the identity and the "
                            + "first partial derivatives. Reindex rows and columns by Option (Fin d), "
                            + "using none for zero and some i for the i-th unit index. The matrix on "
                            + "the monomials 1 and X i is the identity with its first row replaced by "
                            + "the vector consisting of 1 and X i, and its determinant is one.")),
                    Paragraph(Text(
                        "For a homogeneous quadratic p, Euler's identity says that the sum of "
                            + "X i times the i-th partial derivative of p equals 2p. Consequently the "
                            + "column of p and its first partial derivatives is minus p times the "
                            + "constant column plus the sum of the i-th partial derivative of p times "
                            + "the X i column. Determinant multilinearity therefore evaluates a "
                            + "replacement in the constant column as minus p, and a replacement in "
                            + "the X i column as the i-th partial derivative of p. Each replacement "
                            + "stays in the original column position.")),
                    Paragraph(Text(
                        "Take q to be the sum of (X i)^2 over Fin d. It is homogeneous of degree two, "
                            + "and its i-th partial derivative is (2 : K) times X i. Since there is a "
                            + "coordinate and the field has characteristic zero, this also proves q is "
                            + "nonzero. The brackets just evaluated all lie in lonely q: "
                            + "they are 1, minus q, and (2 : K) times X i. The generating-family "
                            + "expansion therefore puts every bracket in lonely q. Conversely, these "
                            + "brackets obtained by omitting one generator have arguments in lonely q. "
                            + "Their span contains 1 and q, and multiplication by the inverse of (2 : K) "
                            + "puts every X i in it. These polynomials generate lonely q, proving the "
                            + "reverse inclusion and hence perfectness.")),
                    Paragraph(Text(
                        "Finally, existence together with k at least one forces k = 1, since every "
                            + "other such natural k is at least two and contradicts the obstruction. "
                            + "When k = 1, the polynomial q supplies nonzeroness, homogeneity and "
                            + "perfectness, proving the converse."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kenins-kiselev-2026-wronskian-perfect-lonely-algebra"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula IndexFormula() => All("d", Naturals(), All("k", Naturals(),
        Equal(Typed(LocalCall("I", X("d"), X("k")), At(Qualified("Finset"), MultiIndex())),
            Seq(OpenBrace, Typed(X("α"), MultiIndex()), Sp, Mid, Sp,
                LE(At(Qualified("Finsupp", "degree"), X("α")), X("k")), CloseBrace))));

    private static Formula PartialFormula()
    {
        Formula derivative = At(Qualified("Derivation", "toLinearMap"),
            At(Qualified("MvPolynomial", "pderiv"), X("i")));
        Formula factors = At(Qualified("List", "map"),
            LambdaOf("i", FinOf(X("d")), new Formula.Power(derivative, At(X("α"), X("i")))),
            At(Qualified("List", "finRange"), X("d")));
        return FieldBinders(All("d", Naturals(), All("α", MultiIndex(),
            Equal(Typed(Partial(X("α")), LinearEndomorphisms()), At(Qualified("List", "prod"), factors)))));
    }

    private static Formula WronskianFormula()
    {
        Formula entry = At(At(Qualified("DFunLike", "coe"),
            Partial(At(Qualified("Subtype", "val"), X("α")))), At(X("f"), X("β")));
        Formula matrix = LambdaOf("α", IndexType(), LambdaOf("β", IndexType(), entry));
        return PolynomialBinders(All("f", Arguments(),
            Equal(Typed(Wronskian(X("f")), Polynomials()), At(Qualified("Matrix", "det"), matrix))));
    }

    private static Formula LonelyFormula() => PolynomialBinders(All("p", Polynomials(),
        Equal(Typed(Lonely(X("p")), At(Qualified("Submodule"), X("K"), Polynomials())),
            At(Qualified("SemilatticeSup", "sup"),
                At(Qualified("MvPolynomial", "restrictTotalDegree"), FinOf(X("d")), X("K"), X("k")),
                At(Qualified("Submodule", "span"), X("K"), Seq(OpenBrace, X("p"), CloseBrace))))));

    private static Formula PerfectFormula()
    {
        Formula values = Seq(OpenBrace, Typed(X("w"), Polynomials()), Sp, Mid, Sp,
            Some("f", Arguments(), AndOf(
                All("β", IndexType(), Member(At(X("f"), X("β")), Lonely(X("p")))),
                Equal(Wronskian(X("f")), X("w")))), CloseBrace);
        return PolynomialBinders(All("p", Polynomials(), IffOf(Perfect(X("p")),
            Equal(At(Qualified("Submodule", "span"), X("K"), values), Lonely(X("p"))))));
    }

    private static Formula ClaimBody()
    {
        Formula extension = Some("p", Polynomials(), AndOf(
            NotEqual(X("p"), Typed(D(0), Polynomials())), AndOf(
                At(Qualified("MvPolynomial", "IsHomogeneous"), X("p"),
                    new Formula.Binary(X("k"), FormulaBinaryOperator.Add, D(1))),
                Perfect(X("p")))));
        Formula dimensions = All("d", Naturals(), All("k", Naturals(),
            Arrow(LE(D(2), X("d")), Arrow(LE(D(1), X("k")),
                IffOf(extension, Equal(X("k"), D(1)))))));
        return All("K", Qualified("Type"), InstanceBinder(At(Qualified("Field"), X("K")),
            InstanceBinder(At(Qualified("CharZero"), X("K")), dimensions)));
    }

    private static Formula FieldBinders(Formula body) => All("K", Seq(Qualified("Type"), Star),
        InstanceBinder(At(Qualified("Field"), X("K")), body));
    private static Formula PolynomialBinders(Formula body) => FieldBinders(
        All("d", Naturals(), All("k", Naturals(), body)));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinOf(Formula d) => At(Qualified("Fin"), d);
    private static Formula MultiIndex() => At(Qualified("Finsupp"), FinOf(X("d")), Naturals());
    private static Formula Polynomials() => At(Qualified("MvPolynomial"), FinOf(X("d")), X("K"));
    private static Formula IndexType() => Seq(OpenBrace, Typed(X("α"), MultiIndex()), Sp,
        Slash, Slash, Sp, Member(X("α"), LocalCall("I", X("d"), X("k"))), CloseBrace);
    private static Formula Arguments() => Arrow(IndexType(), Polynomials());
    private static Formula LinearEndomorphisms() => At(Qualified("LinearMap"),
        At(Qualified("RingHom", "id"), X("K")), Polynomials(), Polynomials());
    private static Formula Partial(Formula α) => LocalCall("pderivMulti",
        NamedArgument("K", X("K")), NamedArgument("d", X("d")), α);
    private static Formula Wronskian(Formula f) => LocalPolynomialCall("wronskian", f);
    private static Formula Lonely(Formula p) => LocalPolynomialCall("lonely", p);
    private static Formula Perfect(Formula p) => LocalPolynomialCall("perfect", p);
    private static Formula LocalPolynomialCall(string name, Formula argument) => LocalCall(name,
        NamedArgument("K", X("K")), NamedArgument("d", X("d")), NamedArgument("k", X("k")), argument);
    private static Formula Local(string name) => Qualified("D5", "S3", "HomologicalAlgebra",
        "WronskianPerfectLonelyAlgebra", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => name switch
    {
        "α" => Alpha,
        "β" => Beta,
        _ => F.Id(name),
    };
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
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula NamedArgument(string name, Formula value) => Parenthesized(Seq(X(name), Colon, Eq, Sp, value));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula InstanceBinder(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula AndOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
}

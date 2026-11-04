using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ThreeDistinguishabilityProductRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/korzekwaetal2019distinguishing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three orthogonal pure states exclude every labelling of the product ansatz.",
        H("The three-distinguishability product conjecture fails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("in-region"),
                DeclarationHandle.Create(Module + ".InRegion"),
                H("The three-distinguishability region"),
                StatementSource.FromAuthor(Disp(InRegionDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A real function p on Fin 4 lies in the region when it belongs to the standard "
                    + "simplex and there are three complex 4 by 4 positive semidefinite matrices of "
                    + "trace one whose pairwise products vanish and whose diagonal real parts all equal p. "
                    + "This is the source's M-distinguishability definition, Distinguishability.tex lines "
                    + "147–149 and 236–241, specialized to d = 4 and M = 3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("product-form"),
                DeclarationHandle.Create(Module + ".ProductForm"),
                H("The two-parameter product form"),
                StatementSource.FromAuthor(Disp(ProductFormDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "ProductForm f p means that p is the convex combination of f 0, f 1, f 2 and f 3 "
                    + "with weights ab, a(1−b), (1−a)b and (1−a)(1−b), for real a and b in the unit "
                    + "interval. The four functions f are supplied separately so that the definition "
                    + "can express any labelling of the face centres. This is equation (30) of the source, "
                    + "Distinguishability.tex lines 462–467."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The labelled product conjecture"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimProposition()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The conjecture asks for one permutation σ of Fin 4 such that every p in the "
                    + "three-distinguishability region has the product form built from the relabelled "
                    + "face centres i ↦ target (σ i). The permutation is existential because the "
                    + "source presents the four face centres with a labelling convention, while the "
                    + "mathematical assertion concerns some labelling."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A counterexample to every labelling"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let r = √5 and let p on Fin 4 have coordinates ((5 − r)/10, (5 − r)/20, "
                        + "(5 − r)/10, (r − 1)/4). The radical bounds 2 < r < 9/4 prove that p has "
                        + "nonnegative coordinates, and direct summation proves that p belongs to the "
                        + "standard simplex.")),
                    Paragraph(Text(
                        "Set ζ = exp((π/5) i) and use the three phase rows in the construction. "
                        + "The identity conj ζ · ζ = 1 gives unit phases, while ζ⁵ = −1 and the quadratic "
                        + "relation ζ² = ((1 + √5)/2)ζ − 1 yield the powers ζ³, ζ⁴, ζ⁷ and ζ⁹ and the "
                        + "conjugate of ζ. Substitution into the weighted sums proves that the three "
                        + "weighted frame vectors are pairwise orthogonal.")),
                    Paragraph(Text(
                        "The diagonal calculation gives each constructed vector xᵢ the coordinate identity "
                        + "xᵢ k · conj(xᵢ k) = p k. "
                        + "Rank-one density matrices built from the three vectors therefore have trace one, "
                        + "are positive semidefinite, have pairwise zero products by orthogonality, and share "
                        + "the diagonal p. Thus p lies in InRegion.")),
                    Paragraph(Text(
                        "For any permutation σ, a product-form representation of p implies the equal-product "
                        + "identity (1 − 3 p (σ 0))(1 − 3 p (σ 3)) = "
                        + "(1 − 3 p (σ 1))(1 − 3 p (σ 2)). The four-element involutive pairing argument "
                        + "transfers this identity to one of the three pairings of the values 1 − 3 p k: "
                        + "(1 − 3 p 0)(1 − 3 p 1) = (1 − 3 p 2)(1 − 3 p 3), "
                        + "(1 − 3 p 0)(1 − 3 p 2) = (1 − 3 p 1)(1 − 3 p 3), or "
                        + "(1 − 3 p 0)(1 − 3 p 3) = (1 − 3 p 1)(1 − 3 p 2).")),
                    Paragraph(Text(
                        "Substituting the four coordinates of p and using (√5)² = 5 shows that all three "
                        + "pairing equalities are false. Hence p has no ProductForm representation for any "
                        + "permutation σ. Applying the asserted claim to p and its InRegion witness gives "
                        + "this impossible product representation, so the claim is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("korzekwa-et-al-2019-three-distinguishability-product-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula InRegionDefinition()
    {
        Formula p = X("p");
        Formula rho = X("ρ");
        Formula matrices = MatrixType(FinOf(D(4)), FinOf(D(4)), Complexes());
        Formula simplex = And(
            All("k", FinOf(D(4)), LessThanOrEqual(Typed(D(0), Reals()), At(p, X("k")))),
            Equal(Seq(new Formula.Subscript(Sum, Typed(X("k"), FinOf(D(4)))),
                Sp, Parenthesized(At(p, X("k")))), Typed(D(1), Reals())));
        Formula density = All("i", FinOf(D(3)), And(
            At(Qualified("Matrix", "PosSemidef"), At(rho, X("i"))),
            Equal(At(Qualified("Matrix", "trace"), At(rho, X("i"))), Typed(D(1), Complexes()))));
        Formula orthogonal = All("i", FinOf(D(3)), All("j", FinOf(D(3)), Imp(
            NotEqual(X("i"), X("j")),
            Equal(Multiply(At(rho, X("i")), At(rho, X("j"))),
                Typed(D(0), matrices)))));
        Formula diagonal = All("i", FinOf(D(3)), All("k", FinOf(D(4)), Equal(
            At(Qualified("Complex", "re"),
                At(Qualified("Matrix", "diag"), At(rho, X("i")), X("k"))),
            At(p, X("k")))));
        Formula witness = Some("ρ", Arrow(FinOf(D(3)), matrices),
            And(density, And(orthogonal, diagonal)));
        return All("p", Arrow(FinOf(D(4)), Reals()),
            Equivalence(LocalCall("InRegion", p), And(simplex, witness)));
    }

    private static Formula ProductFormDefinition()
    {
        Formula f = X("f");
        Formula p = X("p");
        Formula fin4 = FinOf(D(4));
        Formula functionFamily = Arrow(fin4, Arrow(fin4, Reals()));
        Formula vector = Arrow(fin4, Reals());
        Formula fAt(int index) => At(f, Typed(D((byte)index), fin4));
        Formula scalar(Formula value, Formula function) =>
            Seq(Parenthesized(value), Sp, Cdot, Sp, Parenthesized(function));
        Formula term0 = scalar(Multiply(X("a"), X("b")), fAt(0));
        Formula term1 = scalar(Multiply(X("a"), Subtract(Typed(D(1), Reals()), X("b"))), fAt(1));
        Formula term2 = scalar(Multiply(Subtract(Typed(D(1), Reals()), X("a")), X("b")), fAt(2));
        Formula term3 = scalar(Multiply(Subtract(Typed(D(1), Reals()), X("a")),
            Subtract(Typed(D(1), Reals()), X("b"))), fAt(3));
        Formula sum = Add(Add(Add(term0, term1), term2), term3);
        Formula bounds = And(
            LessThanOrEqual(Typed(D(0), Reals()), X("a")),
            And(LessThanOrEqual(X("a"), Typed(D(1), Reals())),
                And(LessThanOrEqual(Typed(D(0), Reals()), X("b")),
                    LessThanOrEqual(X("b"), Typed(D(1), Reals())))));
        return All("f", functionFamily, All("p", vector,
            Equivalence(LocalCall("ProductForm", f, p),
                Some("a", Reals(), Some("b", Reals(),
                    And(bounds, Equal(p, sum)))))));
    }

    private static Formula ClaimProposition()
    {
        Formula sigma = SigmaLower;
        Formula fin4 = FinOf(D(4));
        Formula relabelled = LambdaOf("i", fin4,
            At(Qualified("D5", "S3", "QuantumBounds", "RebitExclusionDistance", "target"),
                At(sigma, X("i"))));
        return Some("σ", At(Qualified("Equiv", "Perm"), fin4),
            All("p", Arrow(fin4, Reals()),
                Imp(LocalCall("InRegion", X("p")),
                    LocalCall("ProductForm", relabelled, X("p")))));
    }

    private static Formula X(string name) => name switch
    {
        "ρ" => Rho,
        "σ" => SigmaLower,
        _ => F.Id(name),
    };

    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Measurements", "ThreeDistinguishabilityProductRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula MatrixType(Formula rows, Formula columns, Formula field) =>
        At(Qualified("Matrix"), rows, columns, field);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class AbsolutelyEntangledAllPartitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/yuetal2021absolutelyentangled");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every composite dimension admits a finite set with one state entangled for all fixed tensor partitions in each frame.",
        H("Simultaneous entanglement for all fixed tensor partitions"),
        Blocks(
            Definition("partition", "Partition", "Ordered nontrivial factorizations", PartitionFormula(),
                "A partition is an ordered list of k natural dimensions, with k at least two, "
                    + "each dimension at least two, and product d. The pair consisting of k and "
                    + "its dimension function is restricted by these three conditions. "
                    + "These are the tensor partitions described in main.tex, line 308 and "
                    + "Definition 3, lines 310–317; factor order is retained."),
            Definition("partition-equiv", "partitionEquiv", "The fixed mixed-radix coordinates", PartitionEquivFormula(),
                "The mixed-radix equivalence first identifies a tuple of local indices with an "
                    + "index below the product of the dimensions, then uses the product equality "
                    + "to identify that index type with Fin d. Thus each ordered factorization "
                    + "has one specified tensor coordinate system. The fixed orthonormal basis "
                    + "in the source's Corollary, main.tex, lines 499–508, motivates fixing "
                    + "these identifications before varying the global unitary.", true),
            Definition("product-state", "productState", "Tensor products in the fixed coordinates", ProductStateFormula(),
                "Given one square complex matrix for each factor, take their tensor product "
                    + "and reindex both matrix coordinates by the inverse mixed-radix equivalence. "
                    + "Equivalently, the entry at two global indices is the product of the local "
                    + "matrix entries at their corresponding local indices. This expresses the "
                    + "tensor product of subsystems in Definition 3(i), main.tex, line 314. "
                    + "The construction accepts arbitrary local matrices, without positivity "
                    + "or trace assumptions."),
            Definition("separable", "Separable", "Full separability for a partition", SeparableFormula(),
                "A matrix is separable for p when it belongs to the real convex hull of tensor "
                    + "products of local positive semidefinite matrices of complex trace one. "
                    + "Thus it is a finite convex combination of local density products. "
                    + "This gives the density-matrix meaning of separability for the tensor "
                    + "partition in Definition 3, main.tex, lines 312–315."),
            Definition("claim", "claim", "One common entangled state after each unitary",
                EqualTo(Local("claim"), Parenthesized(ClaimBody())),
                "For every factorization d = a times b with a and b at least two, there is "
                    + "one finite set s of positive semidefinite complex matrices of trace one. "
                    + "For every special unitary matrix u, some member of s becomes nonseparable "
                    + "for every partition after conjugation by u. The chosen member can depend "
                    + "on u, but must serve all partitions at once. This is the fixed-coordinate "
                    + "reading of the question in main.tex, line 509, with partitions specified "
                    + "by the mixed-radix identifications above.", true),
            Describe.Lean(
                DescribeId.Create("summand-kernel"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.summand_kernel"),
                H("Positive summands annihilate the orthogonal complement"),
                StatementSource.FromAuthor(Disp(SummandKernelFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positively weighted positive semidefinite summand of a real multiple of a rank-one density annihilates every vector orthogonal to its defining vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supported-column"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.supported_column"),
                H("Columns supported on one vector"),
                StatementSource.FromAuthor(Disp(SupportedColumnFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every column of a Hermitian matrix annihilating the orthogonal complement of a nonzero vector is a complex scalar multiple of that vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A finite grid supplies a common entangled state"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For each partition p, vary the first two local indices over zero and "
                            + "one and fix all remaining local indices at zero. The four resulting "
                            + "global coordinates are distinct: the inverse mixed-radix map recovers "
                            + "the first two indices. For any embedding c of Fin 2 times Fin 2 into "
                            + "Fin d, consider the determinant formed from these four coordinates "
                            + "of a vector: the product at c(0,0) and c(1,1) minus the product at "
                            + "c(0,1) and c(1,0).")),
                    Paragraph(Text(
                        "Fix a special unitary u. Each coordinate of ux is a linear polynomial "
                            + "in the coordinates of x, so the determinant just described becomes "
                            + "a polynomial of total degree at most two. It is nonzero: let z be "
                            + "the sum of the coordinate vectors at c(0,0) and c(1,1), and evaluate "
                            + "at u* z. The identity uu* = 1 reduces the value to the determinant "
                            + "of z, which is one because the four coordinates are distinct.")),
                    Paragraph(Text(
                        "A nonzero polynomial of total degree at most m cannot vanish on the "
                            + "whole Cartesian grid with alphabet the complex images of the natural "
                            + "numbers zero through m. Indeed, this alphabet has m + 1 elements. "
                            + "If all grid points were zeros, the Schwartz–Zippel bound would give "
                            + "one at most the total degree divided by m + 1, contradicting the "
                            + "degree bound. Let r be the number of embeddings of Fin 2 times "
                            + "Fin 2 into Fin d and set m = 2r. The product of the determinant "
                            + "polynomials over all these embeddings is nonzero and has total "
                            + "degree at most 2r. Its value at a grid point v is the product of "
                            + "the corresponding determinants of uv. Choose a grid point where "
                            + "this value is nonzero. Then every determinant is nonzero. For d "
                            + "at least four an embedding exists, so v cannot be zero. Hence the "
                            + "same finite grid, with its zero vector removed, works for every u.")),
                    Paragraph(Text(
                        "For every nonzero grid vector v, divide vv* by its real energy, "
                            + "the sum of the squared complex norms of its coordinates. This "
                            + "energy is positive. The outer product is positive semidefinite "
                            + "and its complex trace is the complex image of the energy, so the "
                            + "normalized matrix is positive semidefinite with trace one. "
                            + "Conjugation by u turns it into the outer product of uv multiplied "
                            + "by the same inverse real energy.")),
                    Paragraph(Text(
                        "Tensor products of local density matrices are density matrices. "
                            + "For positivity, induct on the set of local factors: the empty "
                            + "product is the outer product of the constant one vector, and "
                            + "adjoining a factor takes the Hadamard product with its reindexed "
                            + "positive semidefinite matrix. For trace one, sum diagonal entries "
                            + "through the mixed-radix equivalence; the sum of products factors "
                            + "into the product of the local traces. Every column of such a "
                            + "tensor product has zero determinant at the four coordinates "
                            + "associated with p: after distributing the products, the first "
                            + "two local factors agree by commutativity and the other factors "
                            + "are identical.")),
                    Paragraph(Text(
                        "Suppose a nonnegative weighted sum of positive semidefinite matrices "
                            + "equals a real scalar multiple of vv*. If x is orthogonal to v, "
                            + "the quadratic form of this sum at x is zero. Each summand is "
                            + "nonnegative, so a summand with positive weight has zero quadratic "
                            + "form at x and therefore annihilates x. For a Hermitian matrix "
                            + "annihilating every such x and for nonzero v, each column is a "
                            + "complex multiple of v. Explicitly, choose an index i with "
                            + "v(i) nonzero and test the kernel condition on the difference "
                            + "between the k-coordinate vector scaled by the conjugate of v(i) "
                            + "and the i-coordinate vector scaled by the conjugate of v(k). "
                            + "Conjugating the resulting equality and using Hermiticity gives "
                            + "the jth column as v multiplied by its ith entry divided by v(i).")),
                    Paragraph(Text(
                        "Now suppose a real multiple of vv* is separable for p. If v is zero, "
                            + "its four-coordinate determinant is zero directly. Otherwise write "
                            + "the matrix as a finite convex combination of local density products. "
                            + "Some weight is positive because the weights sum to one. The "
                            + "corresponding product matrix has trace one, so some diagonal "
                            + "entry is nonzero. The kernel argument makes that column z times "
                            + "v for a nonzero complex z. Its four-coordinate determinant is "
                            + "zero by the tensor-product calculation, while scaling a two "
                            + "by two determinant multiplies it by z squared. Since z is "
                            + "nonzero, the determinant of v must be zero.")),
                    Paragraph(Text(
                        "Finally, d = a times b with a and b at least two gives d at least "
                            + "four. Take s to be the image of the nonzero finite grid under "
                            + "the normalization v to vv* divided by its energy. All its members "
                            + "are density matrices. Given u, choose the grid vector whose "
                            + "transformed determinants are all nonzero. If its conjugated "
                            + "density matrix were separable for any p, the preceding argument "
                            + "would force the determinant at p's four specified coordinates "
                            + "to vanish. Those coordinates give one of the embeddings already "
                            + "excluded. This proves nonseparability for every p simultaneously."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yu-et-al-2021-absolutely-entangled-all-partitions"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose, bool fromRepo = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            fromRepo ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula SummandKernelFormula()
    {
        Formula index = X("ι");
        Formula vector = Arrow(FinOf(X("d")), Complexes());
        Formula weights = Arrow(index, Reals());
        Formula matrices = Arrow(index, MatrixType());
        Formula nonnegative = All("i", index, LessEqual(Typed(D(0), Reals()), At(X("w"), X("i"))));
        Formula positive = All("i", index, At(Qualified("Matrix", "PosSemidef"), At(X("a"), X("i"))));
        Formula sum = SumOver("i", index, Smul(At(X("w"), X("i")), At(X("a"), X("i"))));
        Formula density = At(Qualified("D5", "S3", "Quantum", "PureState", "PureStateHandshake", "rankOneDensity"), X("v"));
        Formula conclusion = EqualTo(At(Qualified("Matrix", "mulVec"), At(X("a"), X("j")), X("x")),
            Typed(D(0), vector));
        Formula body = All("w", weights, All("a", matrices, Imp(nonnegative, Imp(positive,
            All("v", vector, All("t", Reals(), Imp(EqualTo(sum, Smul(X("t"), density)),
                All("j", index, Imp(new Formula.Relation(Typed(D(0), Reals()),
                    FormulaRelationOperator.LessThan, At(X("w"), X("j"))),
                    All("x", vector, Imp(Orthogonal(), conclusion)))))))))));
        return All("d", Naturals(), All("ι", Qualified("Type"),
            Seq(OpenBracket, At(Qualified("Fintype"), index), CloseBracket, Comma, Sp, Parenthesized(body))));
    }

    private static Formula SupportedColumnFormula()
    {
        Formula vector = Arrow(FinOf(X("d")), Complexes());
        Formula kernel = All("x", vector, Imp(Orthogonal(),
            EqualTo(At(Qualified("Matrix", "mulVec"), X("a"), X("x")), Typed(D(0), vector))));
        Formula column = LambdaOf("k", FinOf(X("d")), At(X("a"), X("k"), X("j")));
        return All("d", Naturals(), All("v", vector,
            Imp(new Formula.Not(Parenthesized(EqualTo(X("v"), Typed(D(0), vector)))),
                All("a", MatrixType(), Imp(At(Qualified("Matrix", "IsHermitian"), X("a")),
                    Imp(kernel, All("j", FinOf(X("d")), Some("z", Complexes(),
                        EqualTo(Parenthesized(column), Smul(X("z"), X("v")))))))))));
    }

    private static Formula Orthogonal() => EqualTo(
        At(Qualified("dotProduct"), At(Qualified("Star", "star"), X("v")), X("x")), Typed(D(0), Complexes()));
    private static Formula Smul(Formula scalar, Formula value) => At(Qualified("SMul", "smul"), scalar, value);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Typed(X(name), type)), Sp, Parenthesized(body));

    private static Formula PartitionFormula()
    {
        Formula dimensions = Seq(Sigma, Sp, Typed(X("k"), Naturals()), Comma, Sp,
            Arrow(FinOf(X("k")), Naturals()));
        Formula conditions = And(LessEqual(D(2), First(X("p"))),
            And(All("i", FinOf(First(X("p"))), LessEqual(D(2), At(Second(X("p")), X("i")))),
                EqualTo(ProductOver("i", FinOf(First(X("p"))), At(Second(X("p")), X("i"))), X("d"))));
        return All("d", Naturals(), EqualTo(LocalCall("Partition", X("d")),
            Seq(OpenBrace, Typed(X("p"), dimensions), Sp, Mid, Sp, conditions, CloseBrace)));
    }

    private static Formula PartitionEquivFormula()
    {
        Formula equalityProof = Second(Second(At(Qualified("Subtype", "property"), X("p"))));
        Formula equivalence = At(Qualified("Equiv", "trans"), Qualified("finPiFinEquiv"),
            At(Qualified("finCongr"), equalityProof));
        Formula type = At(Qualified("Equiv"), IndexTuple(), FinOf(X("d")));
        return WithPartition(EqualTo(Typed(LocalCall("partitionEquiv", X("p")), type), equivalence));
    }

    private static Formula ProductStateFormula()
    {
        Formula product = At(Qualified("D5", "S3", "Quantum", "Recovery", "ProductPrefixRigidity", "productMap"),
            LambdaOf("i", FactorIndex(), LocalIndex(X("i"))), Rho);
        Formula inverse = At(Qualified("Equiv", "symm"), LocalCall("partitionEquiv", X("p")));
        Formula inverseFunction = At(Qualified("Equiv", "toFun"), inverse);
        return WithPartition(All("ρ", LocalMatrices(),
            EqualTo(LocalCall("productState", X("p"), Rho),
                At(Qualified("Matrix", "submatrix"), product, inverseFunction, inverseFunction))));
    }

    private static Formula SeparableFormula()
    {
        Formula products = Seq(OpenBrace, Typed(X("σ"), MatrixType()), Sp, Mid, Sp,
            Some("τ", LocalMatrices(), And(All("i", FactorIndex(), Density(At(Tau, X("i")))),
                EqualTo(X("σ"), LocalCall("productState", X("p"), Tau)))), CloseBrace);
        return WithPartition(All("ρ", MatrixType(), EqualTo(LocalCall("Separable", X("p"), Rho),
            Member(Rho, At(Qualified("convexHull"), Reals(), products)))));
    }

    private static Formula ClaimBody()
    {
        Formula densities = All("ρ", MatrixType(), Imp(Member(Rho, X("s")), Density(Rho)));
        Formula conjugate = Multiply(Multiply(X("u"), Rho), At(Qualified("Star", "star"), X("u")));
        Formula entangled = All("p", LocalCall("Partition", X("d")),
            new Formula.Not(Parenthesized(LocalCall("Separable", X("p"), conjugate))));
        Formula frames = All("u", MatrixType(),
            Imp(Member(X("u"), At(Qualified("Matrix", "specialUnitaryGroup"), FinOf(X("d")), Complexes())),
                Some("ρ", MatrixType(), And(Member(Rho, X("s")), entangled))));
        Formula existence = Some("s", At(Qualified("Finset"), MatrixType()), And(densities, frames));
        Formula hypotheses = Imp(LessEqual(D(2), X("a")), Imp(LessEqual(D(2), X("b")),
            Imp(EqualTo(X("d"), Multiply(X("a"), X("b"))), existence)));
        return All("d", Naturals(), All("a", Naturals(), All("b", Naturals(), hypotheses)));
    }

    private static Formula Density(Formula matrix) => And(At(Qualified("Matrix", "PosSemidef"), matrix),
        EqualTo(At(Qualified("Matrix", "trace"), matrix), Typed(D(1), Complexes())));
    private static Formula WithPartition(Formula body) => All("d", Naturals(),
        All("p", LocalCall("Partition", X("d")), body));
    private static Formula FactorIndex() => FinOf(First(At(Qualified("Subtype", "val"), X("p"))));
    private static Formula LocalIndex(Formula i) => FinOf(At(Second(At(Qualified("Subtype", "val"), X("p"))), i));
    private static Formula IndexTuple() => DependentArrow("i", FactorIndex(), LocalIndex(X("i")));
    private static Formula LocalMatrices() => DependentArrow("i", FactorIndex(),
        At(Qualified("Matrix"), LocalIndex(X("i")), LocalIndex(X("i")), Complexes()));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("d")), FinOf(X("d")), Complexes());
    private static Formula First(Formula pair) => Seq(Parenthesized(pair), Dot, D(1));
    private static Formula Second(Formula pair) => Seq(Parenthesized(pair), Dot, D(2));
    private static Formula Local(string name) => Qualified(name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => name switch
    {
        "ι" => Iota,
        "ρ" => Rho,
        "σ" => SigmaLower,
        "τ" => Tau,
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
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula dimension) => At(Qualified("Fin"), dimension);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula DependentArrow(string name, Formula domain, Formula codomain) =>
        Arrow(Typed(X(name), domain), codomain);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(Prod, Underscore, Grp(Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula EqualTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula element, Formula set) => new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}

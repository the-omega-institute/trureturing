using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class DensityTensorNuclearNormEqualityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/derksenfriedlandlimwang2017entanglement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mixed flagged Bell density tensor attains the conjectured nuclear-norm maximum.",
        H("Refuting the density-tensor nuclear-norm equality conjecture"),
        Blocks(
            Node("nuclear-norm", "The complex nuclear norm", NuclearNormFormula(),
                "For a finite mode type κ, nuclearNorm is Mathlib's projective tensor norm of the tensor whose coefficients are t in the product of the standard Euclidean bases. Basis.piTensorProduct constructs this product basis, and its equivFun.symm sends the coefficient array to the tensor. Mathlib supplies the infimum over finite product decompositions, with Euclidean factor norms, matching the source's definition at TeX lines 494–497.",
                "nuclearNorm", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("alpha", "The maximal nuclear norm of unit tensors", AlphaFormula(),
                "For a finite mode type κ and mode sizes m, alpha is the supremum of nuclearNorm over coefficient tensors whose Mathlib Euclidean norm is one. This is the source's α(n,ℂ) definition at TeX lines 525–526.",
                "alpha", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("density-tensor", "A matrix as a doubled density tensor", DensityTensorFormula(),
                "The matrix indexed by tuples over Fin d is read as a tensor with separate row and column modes. At an index in Fin d ⊕ Fin d, the inl coordinates select the matrix row and the inr coordinates select its column. This is the density-tensor construction described at TeX lines 680–695.",
                "densityTensor", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The equality-case conjecture", ClaimFormula(),
                "For every number of modes, mode-size function and positive semidefinite trace-one complex matrix, equality of the doubled density tensor's nuclear norm with alpha squared is asserted to produce a tensor t with Mathlib Euclidean norm one whose nuclear norm is alpha and whose rank-one density matrix is the given matrix. This is the repository's formal reading of the equality conjecture stated at TeX line 878.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A mixed equality-case counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Set n to the two-mode size function [2, 4] and identify its index type with Fin 2 × Fin 4. "
                            + "For b in Fin 2, let v b place the coefficient (√2)⁻¹ on the two positions whose second coordinate is the first coordinate plus 2b, and put zero elsewhere. "
                            + "The two vectors have Euclidean norm one. Define a as one half of the sum of the two rank-one matrices vecMulVec (v b) (star (v b)). Their Gram matrix is the identity, so a is positive semidefinite and has trace one.")),
                    Paragraph(Text(
                        "The row decomposition of any tensor of shape (2,4) gives nuclearNorm at most √2 times its Euclidean norm. "
                            + "For v 0, the linear functional that adds the (0,0) and (1,1) entries has norm at most one on every product tensor and takes v 0 to √2. "
                            + "The dual bound therefore gives nuclearNorm (v 0) = √2. The row upper bound applies to every Euclidean-unit tensor, while v 0 attains it, so alpha n = √2.")),
                    Paragraph(Text(
                        "Expand densityTensor a into eight product tensors, one for each choice of the two flagged Bell components and their four mode coordinates. Each product has nuclear cost 1/4, giving the upper bound nuclearNorm (densityTensor a) ≤ 2. "
                            + "For the reverse inequality, use the four-mode linear functional that sums the two Bell contractions in each flag block. Its value on a product tensor is bounded by Cauchy–Schwarz after splitting the second and fourth factors into their two two-coordinate blocks; the resulting bound is the product of the four Euclidean norms. The functional takes densityTensor a to 2, so the dual bound gives nuclearNorm (densityTensor a) ≥ 2.")),
                    Paragraph(Text(
                        "Consequently nuclearNorm (densityTensor a) = 2 = alpha n squared. If claim held, its witness t would have unit Euclidean norm and would satisfy a = vecMulVec t (star t). The unit norm makes this rank-one matrix idempotent, so a squared would equal a. Direct multiplication of the two orthogonal flagged rank-one summands instead gives a squared = (1/2) • a. Since a has trace one and is nonzero, these equalities contradict each other. Thus the equality case need not be a pure density state."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("derksen-friedland-lim-wang-2017-density-tensor-nuclear-norm-equality"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("density-tensor-nuclear-norm-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula NuclearNormFormula()
    {
        Formula modes = Kappa;
        Formula m = X("m");
        Formula tensor = TensorType(modes, m);
        Formula basis = At(Qualified("Basis", "piTensorProduct"),
            LambdaOf(X("j"), modes,
                At(Qualified("PiLp", "basisFun"), D(2), Complexes(), FinOf(At(m, X("j"))))));
        Formula image = At(Qualified("LinearEquiv", "symm"),
            At(Qualified("Basis", "equivFun"), basis), X("t"));
        Formula body = Equal(LocalCall("nuclearNorm", m, X("t")), Norm(image));
        return All(modes, TypeUniverse(), WithFintype(modes,
            All(m, Arrow(modes, Naturals()),
                All(X("t"), tensor, body))));
    }

    private static Formula AlphaFormula()
    {
        Formula modes = Kappa;
        Formula m = X("m");
        Formula tensor = TensorType(modes, m);
        Formula set = SetOf(X("s"), Reals(),
            Exists(X("t"), tensor,
                And(Equal(Norm(At(Qualified("WithLp", "toLp"), D(2), X("t"))), Typed(D(1), Reals())),
                    Equal(X("s"), LocalCall("nuclearNorm", m, X("t"))))));
        return All(modes, TypeUniverse(), WithFintype(modes,
            All(m, Arrow(modes, Naturals()),
                Equal(LocalCall("alpha", m), At(Qualified("sSup"), set)))));
    }

    private static Formula DensityTensorFormula()
    {
        Formula d = X("d");
        Formula n = X("n");
        Formula index = PiType(X("j"), At(Qualified("Fin"), d),
            FinOf(At(n, X("j"))));
        Formula doubled = At(Qualified("Sum"), FinOf(d), FinOf(d));
        Formula doubledIndex = PiType(X("j"), doubled,
            FinOf(At(Qualified("Sum", "elim"), n, n, X("j"))));
        Formula body = LambdaOf(X("i"), doubledIndex,
            At(X("a"),
                LambdaOf(X("j"), At(Qualified("Fin"), d),
                    At(X("i"), At(Qualified("Sum", "inl"), X("j")))),
                LambdaOf(X("j"), At(Qualified("Fin"), d),
                    At(X("i"), At(Qualified("Sum", "inr"), X("j"))))));
        return All(d, Naturals(), All(n, Arrow(FinOf(d), Naturals()),
            All(X("a"), Matrix(index, index, Complexes()),
                Equal(LocalCall("densityTensor", X("a")), body))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = X("d");
        Formula n = X("n");
        Formula matrixIndex = PiType(X("j"), FinOf(d), FinOf(At(n, X("j"))));
        Formula matrix = Matrix(matrixIndex, matrixIndex, Complexes());
        Formula density = LocalCall("densityTensor", X("a"));
        Formula doubled = At(Qualified("Sum", "elim"), n, n);
        Formula equality = Equal(
            LocalCall("nuclearNorm", doubled, density),
            new Formula.Power(LocalCall("alpha", n), D(2)));
        Formula conclusion = Exists(X("t"), Arrow(matrixIndex, Complexes()),
            And(Equal(Norm(At(Qualified("WithLp", "toLp"), D(2), X("t"))), Typed(D(1), Reals())),
                And(Equal(LocalCall("nuclearNorm", n, X("t")), LocalCall("alpha", n)),
                    Equal(X("a"), At(Qualified("Matrix", "vecMulVec"), X("t"),
                        At(Qualified("star"), X("t")))))));
        Formula body = All(d, Naturals(), All(n, Arrow(FinOf(d), Naturals()),
            All(X("a"), matrix,
                Implies(At(Qualified("Matrix", "PosSemidef"), X("a")),
                    Implies(Equal(At(Qualified("Matrix", "trace"), X("a")), Typed(D(1), Complexes())),
                        Implies(equality, conclusion))))));
        return Equal(Local("claim"), Parenthesized(body));
    }

    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Entanglement", "Witness",
        "DensityTensorNuclearNormEqualityRefutation", name);

    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);

    private static Formula X(string name) => name switch
    {
        "κ" => Kappa,
        _ => F.Id(name),
    };

    private static Formula Kappa => FormulaDsl.Kappa;
    private static Formula TypeUniverse() => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Matrix(Formula rows, Formula columns, Formula scalar) =>
        At(Qualified("Matrix"), rows, columns, scalar);
    private static Formula TensorType(Formula modes, Formula m) =>
        Arrow(PiType(X("j"), modes, FinOf(At(m, X("j")))), Complexes());
    private static Formula PiType(Formula variable, Formula domain, Formula codomain) =>
        Seq(Parenthesized(Seq(variable, Colon, Sp, domain)), Sp, To, Sp, codomain);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Exists(Formula variable, Formula type, Formula body) =>
        Seq(FormulaDsl.Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula WithFintype(Formula variable, Formula body) =>
        Seq(OpenBracket, At(Qualified("Fintype"), variable), CloseBracket, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(Formula variable, Formula type, Formula body) =>
        Seq(OpenBrace, Typed(variable, type), Sp, Mid, Sp, Parenthesized(body), CloseBrace);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
            {
                items.Add(Dot);
            }
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}

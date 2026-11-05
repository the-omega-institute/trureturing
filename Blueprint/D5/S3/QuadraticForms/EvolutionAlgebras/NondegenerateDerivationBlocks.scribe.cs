using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class NondegenerateDerivationBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stabilizer kernels and derivation blocks of nondegenerate evolution algebras.",
        H("Derivation blocks of nondegenerate evolution algebras"),
        Blocks(
            Describe.Lean(DescribeId.Create("reduced-block-space"), DeclarationHandle.Create(
                Prefix + "reducedBlockSpace"), H("The actual nondegenerate reduced block space"),
                StatementSource.FromAuthor(Disp(ReducedBlockFormula(false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a field k, a k-vector space V, a finite index type I, an arbitrary class index type alpha, a basis b, a class label and square representatives w, put B equal to the standard symmetric form on the coordinate space of the fiber over a, W equal to blockW(b,label,w,a), and U equal to the B-orthogonal complement of W. The reduced space is the actual quotient U/ker(B restricted to U), with its canonical additive group, k-module and finite-dimensional structure. This definition permits empty fibers and degenerate or isotropic W."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reduced-block-form"), DeclarationHandle.Create(
                Prefix + "reducedBlockForm"), H("The induced nondegenerate block form"),
                StatementSource.FromAuthor(Disp(ReducedBlockFormula(true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the actual reduced block quotient, the induced bilinear form evaluates representatives by the restriction of B to U. The kernel has been divided out, so the form is nondegenerate. The canonical pointwise-stabilizer quotient construction supplies its symmetry, nondegeneracy and the surjective reduced Lie action used below."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reduced-block-lie"), DeclarationHandle.Create(
                Prefix + "reducedBlockLie"), H("The actual reduced orthogonal Lie algebra"),
                StatementSource.FromAuthor(Disp(ReducedBlockLieFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the actual Lie subalgebra of skew-adjoint endomorphisms for the reduced block form, with its inherited commutator and k-linear structure. Naming its carrier and canonical Lie instances shares the same mathematical object throughout the dependent product and the full derivation action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-reduced-surjection"), DeclarationHandle.Create(
                Prefix + "nonzero_square_reduced_orthogonal_surjection"), H("Full derivations and nondegenerate reduced blocks"),
                StatementSource.FromAuthor(Disp(FullReducedFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over an algebraically closed field of characteristic zero, every finite natural basis with nonzero squares admits a normalization and an actual surjective Lie map from all actual derivations to the product of the reduced block skew algebras. The kernel is solvable. The map subtracts each class scalar diagonal before applying the canonical setwise-preserver quotient action. Pointwise-stabilizer lifts prove surjectivity. The common diagonal and reduced kernel embeds into a product of canonical kernels with zero triple brackets, and the remaining diagonal quotient is abelian. Every small, empty, isotropic and degenerate block is retained here; no semisimplicity hypothesis on derivations is imposed. The original semisimple full block decomposition remains a separate theorem with its original hypotheses. This is part of the supplied Ma-then-Zhang credited argument; the linear and Lie constructions retain classical credit."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mul-basis-right"),
                DeclarationHandle.Create(Prefix + "mul_basis_right"),
                H("Multiplication by a natural basis vector on the right"),
                StatementSource.FromAuthor(Disp(NaturalProductContext(All(X("x"),X("V"),All(X("j"),Iota,
                    Eq(Apply(Mu,X("x"),Apply(X("b"),X("j"))),
                        Smul(Apply(Seq(X("b"),Dot,Name("repr")),X("x"),X("j")),
                            Apply(Mu,Apply(X("b"),X("j")),Apply(X("b"),X("j")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a field k, a k-vector space V, a bilinear product mu and a finite natural basis b indexed by I, mu(x,b(j)) is the j-th coordinate of x times mu(b(j),b(j)). Expanding x in b eliminates every mixed product. The derivation equations and ideal arguments use this formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mul-basis-left"),
                DeclarationHandle.Create(Prefix + "mul_basis_left"),
                H("Multiplication by a natural basis vector on the left"),
                StatementSource.FromAuthor(Disp(NaturalProductContext(All(X("x"),X("V"),All(X("i"),Iota,
                    Eq(Apply(Mu,Apply(X("b"),X("i")),X("x")),
                        Smul(Apply(Seq(X("b"),Dot,Name("repr")),X("x"),X("i")),
                            Apply(Mu,Apply(X("b"),X("i")),Apply(X("b"),X("i")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same field, vector-space, bilinear-product, finite-index and natural-basis hypotheses, mu(b(i),x) is the i-th coordinate of x times mu(b(i),b(i)). This uses zero mixed products without assuming associativity or a unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pi-piliering"),
                DeclarationHandle.Create(Prefix + "piLieRing"),
                H("piLieRing"),
                StatementSource.FromAuthor(Disp(All(Alpha, Type, All(X("H"), Arrow(Alpha, Type), Instance(All(X("a"), Alpha, Call("LieRing", Apply(X("H"), X("a")))), Eq(Seq(Apply(Qualified("Pi", "piLieRing"), X("H")), Sp, Colon, Sp, Call("LieRing", All(X("a"), Alpha, Apply(X("H"), X("a"))))), Seq(OpenBrace, Call("inferInstance"), Sp, Colon, Sp, Call("AddCommGroup", All(X("a"), Alpha, Apply(X("H"), X("a")))), Sp, Name("with"), Sp, Name("bracket"), Sp, Colon, F.Eq, Sp, Fn(X("f"), Fn(X("g"), Fn(X("a"), Lie(Apply(X("f"), X("a")), Apply(X("g"), X("a")))))), CloseBrace))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The dependent product has the pointwise Lie bracket and the existing pointwise additive group. Its Lie identities hold at every coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pi-piliealgebra"),
                DeclarationHandle.Create(Prefix + "piLieAlgebra"),
                H("piLieAlgebra"),
                StatementSource.FromAuthor(Disp(All(X("k"), Type, Instance(Call("CommRing", X("k")), All(Alpha, Type, All(X("H"), Arrow(Alpha, Type), Instance(All(X("a"), Alpha, Call("LieRing", Apply(X("H"), X("a")))), Instance(All(X("a"), Alpha, Call("LieAlgebra", X("k"), Apply(X("H"), X("a")))), Eq(Seq(Apply(Qualified("Pi", "piLieAlgebra"), X("k"), X("H")), Sp, Colon, Sp, Call("LieAlgebra", X("k"), All(X("a"), Alpha, Apply(X("H"), X("a"))))), Seq(OpenBrace, Parenthesized(Seq(Call("inferInstance"), Sp, Colon, Sp, Call("Module", X("k"), All(X("a"), Alpha, Apply(X("H"), X("a")))))), Sp, Name("with"), CloseBrace)))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The dependent product extends the existing pointwise module with the coordinatewise proof of compatibility between the Lie bracket and scalar multiplication. The record has no additional data fields."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("blocklinear-pidirectsumequiv"),
                DeclarationHandle.Create(Prefix + "piDirectSumEquiv"),
                H("piDirectSumEquiv"),
                StatementSource.FromAuthor(Disp(All(X("k"), Type, Instance(Call("Field", X("k")), All(Beta, Type, Instance(Call("Fintype", Beta), All(X("H"), Arrow(Beta, Type), Instance(All(X("a"), Beta, Call("LieRing", Apply(X("H"), X("a")))), Instance(All(X("a"), Beta, Call("LieAlgebra", X("k"), Apply(X("H"), X("a")))), Eq(Apply(Qualified("BlockLinear", "piDirectSumEquiv"), X("H")), Seq(OpenBrace, Name("toLinearEquiv"), Sp, Colon, F.Eq, Sp, Apply(Qualified("DirectSum", "linearEquivFunOnFintype"), X("k"), Beta, X("H")), Dot, Name("symm"), CloseBrace))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a finite index type, the standard linear equivalence from products to direct sums preserves the componentwise Lie bracket."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("decomposition-blockw"),
                DeclarationHandle.Create(Prefix + "blockW"),
                H("blockW"),
                StatementSource.FromAuthor(Disp(AlgebraContext(All(Iota, Type, All(X("b"), Basis(Iota, X("V")), All(Alpha, Type, All(X("label"), Arrow(Iota, Alpha), All(X("w"), Arrow(Alpha, X("V")), All(X("a"), Alpha, Eq(Apply(Qualified("Decomposition", "blockW"), X("b"), X("label"), X("w"), X("a")), Apply(Qualified("Submodule", "span"), X("k"), Apply(Qualified("Set", "range"), Fn(X("c"), FnTyped(X("i"), Fiber(X("label"), X("a"), Iota), Apply(Seq(X("b"), Dot, Name("repr")), Apply(X("w"), X("c")), Val(X("i"))))))))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The subspace in each block is spanned by the coordinate restrictions of all square representatives."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rescaling-squarerepresentative"),
                DeclarationHandle.Create(Prefix + "squareRepresentative"),
                H("squareRepresentative"),
                StatementSource.FromAuthor(Disp(ProductContext(All(Iota, Type, All(X("b"), Basis(Iota, X("V")), All(X("a"), Lines, Eq(Apply(Representative, X("a")), Apply(Mu, Apply(X("b"), Apply(Qualified("Classical", "choose"), Apply(Seq(X("a"), Dot, Name("property"))))), Apply(X("b"), Apply(Qualified("Classical", "choose"), Apply(Seq(X("a"), Dot, Name("property"))))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each line spanned by a natural square, choose one basis index generating that line and take its square."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("blocks-nonzero-square-diagonal-kernel-decomposition"),
                DeclarationHandle.Create(Prefix + "nonzero_square_diagonal_kernel_decomposition"),
                H("The diagonal kernel without semisimplicity"),
                StatementSource.FromAuthor(Disp(ProductContext(
                    Instance(Call("IsAlgClosed", X("k")), Instance(Call("CharZero", X("k")),
                    All(Iota, Type, Instance(Call("Fintype", Iota), All(X("b"), Basis(Iota, X("V")),
                    Hyp(Natural(X("b"), Iota),
                    Hyp(All(X("i"), Iota, Ne(Apply(Mu, Apply(X("b"), X("i")), Apply(X("b"), X("i"))), D(0))),
                    Some(Seq(X("b"), Apos), Basis(Iota, X("V")),
                        And(Natural(Seq(X("b"), Apos), Iota),
                        And(All(X("i"), Iota, Eq(
                            Apply(Mu, Apply(Seq(X("b"), Apos), X("i")), Apply(Seq(X("b"), Apos), X("i"))),
                            Apply(Representative, Apply(Label, X("i"))))),
                        Some(X("K"), Call("LieIdeal", X("k"), Der),
                            And(Call("IsLieAbelian", Call("Quotient", Der, X("K"))),
                                Nonempty(LieEquivalence(X("K"), Sum(X("a"), Lines,
                                    Call("stabilizer", MatrixForm(Fiber(Label, X("a"), Iota)),
                                        BlockSpan(Seq(X("b"), Apos))))))))))))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Over an algebraically closed field of characteristic zero, let mu be any bilinear product on a vector space with a finite natural basis whose squares are all nonzero. Normalize those squares within their proportionality classes. The diagonal coefficients define an actual Lie homomorphism from derivations to the abelian algebra of scalar coordinate functions: every commutator has zero diagonal. Its actual kernel K is Lie equivalent to the finite direct sum of skew endomorphisms in each class that kill all projected square representatives. Thus Der(mu)/K is abelian, even when Der(mu) is not semisimple. Empty natural bases and empty sums are allowed. The kernel K here is not identified with the solvable radical, and this theorem does not yet give the radical quotient or the simple-ideal classification. The argument factors the existing general derivation equations, class normalization, assembly and restriction proofs; it does not remove the semisimplicity hypothesis from the existing full block equivalence. The underlying evolution-algebra source is the Ma-then-Zhang credited KMV note, alongside standard orthogonal Lie-algebra constructions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("blocks-nonzero-square-block-decomposition"),
                DeclarationHandle.Create(Prefix + "nonzero_square_block_decomposition"),
                H("nonzero square block decomposition"),
                StatementSource.FromAuthor(Disp(ProductContext(Instance(Call("IsAlgClosed", X("k")), All(Iota, Type, Instance(Call("Fintype", Iota), All(X("b"), Basis(Iota, X("V")), Instance(Apply(Qualified("LieAlgebra", "IsSemisimple"), X("k"), Der), Hyp(Natural(X("b"), Iota), Hyp(All(X("i"), Iota, Ne(Apply(Mu, Apply(X("b"), X("i")), Apply(X("b"), X("i"))), D(0))), Some(Seq(X("b"), Apos), Basis(Iota, X("V")), And(Natural(Seq(X("b"), Apos), Iota), And(All(X("i"), Iota, Eq(Apply(Mu, Apply(Seq(X("b"), Apos), X("i")), Apply(Seq(X("b"), Apos), X("i"))), Apply(Representative, Apply(Label, X("i"))))), Nonempty(LieEquivalence(Der, Sum(X("a"), Lines, Call("stabilizer", MatrixForm(Fiber(Label, X("a"), Iota)), BlockSpan(Seq(X("b"), Apos))))))))))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Rescaling the natural basis makes squares identical within each proportionality class. Perfectness eliminates diagonal coefficients of derivations. Independent skew maps killing the projected squares then give all derivations, including the converse construction."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula content) =>Seq(Open, content, Close);
    private static Formula X(string name) =>F.Id(name);
    private static Formula Name(string name) =>Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) =>Seq(Name(owner), Dot, Name(name));
    private static Formula Apply(Formula f, params Formula[] args) =>new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>Apply(Name(name), args);
    private static Formula All(Formula x, Formula type, Formula body) =>Seq(Forall, Sp, Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Hyp(Formula hypothesis, Formula body) =>Imp(hypothesis, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>Seq(Exists, Sp, Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula FnTyped(Formula x, Formula type, Formula body) =>Parenthesized(Seq(Name("fun"), Sp, Parenthesized(Seq(x, Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Fn(Formula x, Formula body) =>Parenthesized(Seq(Name("fun"), Sp, x, Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Ne(Formula a, Formula b) =>new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Val(Formula a) =>Call("val", a);
    private static Formula LMap(Formula a, Formula b) =>Call("LinearMap", X("k"), a, b);
    private static Formula Type =>Name("Type");
    private static Formula Product =>LMap(X("V"), LMap(X("V"), X("V")));
    private static Formula Der =>Call("derivations", Mu);
    private static Formula Lie(Formula a, Formula b) =>Apply(Qualified("Bracket", "bracket"), a, b);
    private static Formula LieEquivalence(Formula a, Formula b) =>Call("LieEquiv", X("k"), a, b);
    private static Formula Sum(Formula i, Formula type, Formula body) =>Call("DirectSum", type, Fn(i, body));
    private static Formula Nonempty(Formula t) =>Call("Nonempty", t);
    private static Formula ReducedBlockFormula(bool form)
    {
        var args = new Formula[] { X("b"), X("label"), X("w"), X("a") };
        var left = Apply(Qualified("Decomposition", form ? "reducedBlockForm" : "reducedBlockSpace"), args);
        var standard = MatrixForm(Fiber(X("label"), X("a"), Iota));
        var fixedSpace = Apply(Qualified("Decomposition", "blockW"), args);
        var complement = Call("orthogonal", standard, fixedSpace);
        Formula body = form
            ? All(X("x"), complement, All(X("y"), complement,
                Eq(Apply(left, Call("quotientClass", X("x")), Call("quotientClass", X("y"))),
                    Apply(standard, Val(X("x")), Val(X("y"))))))
            : Eq(left, Call("Quotient", complement, Call("ker", Call("restrict", standard, complement))));
        body = All(X("a"), Alpha, body);
        body = All(X("w"), Arrow(Alpha, X("V")), body);
        body = All(X("label"), Arrow(Iota, Alpha), body);
        body = All(X("b"), Basis(Iota, X("V")), body);
        body = All(Alpha, Type, body);
        body = All(Iota, Type, Instance(Call("Fintype", Iota), body));
        return AlgebraContext(body);
    }
    private static Formula ReducedBlockLieFormula()
    {
        var args = new Formula[] { X("b"), X("label"), X("w"), X("a") };
        Formula body = All(X("a"), Alpha,
            Eq(Apply(Qualified("Decomposition", "reducedBlockLie"), args),
                Call("skewAdjointLieSubalgebra", Apply(Qualified("Decomposition", "reducedBlockForm"), args))));
        body = All(X("w"), Arrow(Alpha, X("V")), body);
        body = All(X("label"), Arrow(Iota, Alpha), body);
        body = All(X("b"), Basis(Iota, X("V")), body);
        return AlgebraContext(All(Iota, Type, Instance(Call("Fintype", Iota), All(Alpha, Type, body))));
    }
    private static Formula FullReducedFormula()
    {
        var bp = Seq(X("b"), Apos);
        var reduced = Apply(Qualified("Decomposition", "reducedBlockForm"), bp, Label, Representative, X("a"));
        var target = All(X("a"), Lines, Call("skewAdjointLieSubalgebra", reduced));
        Formula body = Some(X("f"), Call("LieHom", X("k"), Der, target),
            And(Apply(Qualified("Function", "Surjective"), X("f")),
                Apply(Qualified("LieAlgebra", "IsSolvable"), Apply(Qualified("LieHom", "ker"), X("f")))));
        body = Some(bp, Basis(Iota, X("V")), And(Natural(bp, Iota), body));
        body = Hyp(All(X("i"), Iota, Ne(Apply(Mu, Apply(X("b"), X("i")), Apply(X("b"), X("i"))), D(0))), body);
        body = Hyp(Natural(X("b"), Iota), body);
        body = All(X("b"), Basis(Iota, X("V")), body);
        body = All(Iota, Type, Instance(Call("Fintype", Iota), body));
        return ProductContext(Instance(Call("IsAlgClosed", X("k")), Instance(Call("CharZero", X("k")), body)));
    }
    private static Formula AlgebraContext(Formula body) =>All(X("k"), Type, Instance(Call("Field", X("k")), All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", X("k"), X("V")), body)))));
    private static Formula ProductContext(Formula body) =>AlgebraContext(All(Mu, Product, body));
    private static Formula NaturalProductContext(Formula body) =>ProductContext(All(Iota,Type,
        All(X("b"),Basis(Iota,X("V")),Hyp(Natural(X("b"),Iota),Instance(Call("Fintype",Iota),body)))));
    private static Formula Smul(Formula a,Formula b) =>Seq(a,Sp,Cdot,Sp,b);
    private static Formula Basis(Formula index, Formula v) =>Apply(Qualified("Module", "Basis"), index, X("k"), v);
    private static Formula Natural(Formula b, Formula index) =>All(X("i"), index, All(X("j"), index, Imp(Ne(X("i"), X("j")), Eq(Apply(Mu, Apply(b, X("i")), Apply(b, X("j"))), D(0)))));
    private static Formula MatrixForm(Formula n) =>Apply(Seq(Name("Matrix"), Dot, new Formula.Subscript(Name("toLinearMap"), D(2)), Apos), X("k"), Seq(D(1), Sp, Colon, Sp, Call("Matrix", n, n, X("k"))));
    private static Formula Fiber(Formula label, Formula a, Formula index) =>Seq(OpenBrace, X("i"), Sp, Colon, Sp, index, Sp, Mid, Sp, Eq(Apply(label, X("i")), a), CloseBrace);
    private static Formula Lines =>Apply(Qualified("Set", "range"), Fn(X("i"), Seq(X("k"), Sp, Cdot, Sp, Apply(Mu, Apply(X("b"), X("i")), Apply(X("b"), X("i"))))));
    private static Formula Label =>Apply(Qualified("Set", "rangeFactorization"), Fn(X("i"), Seq(X("k"), Sp, Cdot, Sp, Apply(Mu, Apply(X("b"), X("i")), Apply(X("b"), X("i"))))));
    private static Formula Representative =>Apply(Qualified("Rescaling", "squareRepresentative"), Mu, X("b"));
    private static Formula BlockSpan(Formula b) =>Apply(Qualified("Decomposition", "blockW"), b, Label, Representative, X("a"));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class OrthogonalPointwiseStabilizersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal pointwise stabilizers.",
        H("Orthogonal pointwise stabilizers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stabilizer-stabilizer"),
                DeclarationHandle.Create(Prefix + "stabilizer"),
                H("stabilizer"),
                StatementSource.FromAuthor(Disp(AlgebraContext(All(X("B"), Bilin, All(X("W"), Submodule, Eq(Call("stabilizer", X("B"), X("W")), Seq(OpenBrace, X("f"), Sp, Colon, Sp, Apply(Qualified("Module", "End"), X("k"), X("V")), Sp, Mid, Sp, And(Member(X("f"), Call("skewAdjointLieSubalgebra", X("B"))), All(X("w"), X("V"), Imp(Member(X("w"), X("W")), Eq(Apply(X("f"), X("w")), D(0))))), CloseBrace))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("This Lie subalgebra consists of skew-adjoint endomorphisms that vanish on the specified subspace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stabilizer-quotientform-symm"),
                DeclarationHandle.Create(Prefix + "quotientForm_symm"),
                H("quotientForm symm"),
                StatementSource.FromAuthor(Disp(FormContext(Apply(Seq(Parenthesized(QuotientForm), Dot, Name("IsSymm")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The form induced on the orthogonal subspace modulo its restricted radical is symmetric."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stabilizer-quotientform-nondegenerate"),
                DeclarationHandle.Create(Prefix + "quotientForm_nondegenerate"),
                H("quotientForm nondegenerate"),
                StatementSource.FromAuthor(Disp(FormContext(Apply(Seq(Parenthesized(QuotientForm), Dot, Name("Nondegenerate")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The form induced on the orthogonal subspace modulo its restricted radical is nondegenerate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stabilizer-stabilizer-equiv-of-trivialradical"),
                DeclarationHandle.Create(Prefix + "stabilizer_equiv_of_trivialRadical"),
                H("stabilizer equiv of trivialRadical"),
                StatementSource.FromAuthor(Disp(FormContext(Instance(Call("FiniteDimensional", X("k"), X("V")), Hyp(Apply(Seq(X("B"), Dot, Name("Nondegenerate"))), Instance(Apply(Qualified("LieAlgebra", "HasTrivialRadical"), X("k"), Call("stabilizer", X("B"), X("W"))), Nonempty(LieEquivalence(Call("stabilizer", X("B"), X("W")), Call("skewAdjointLieSubalgebra", QuotientForm))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Restriction to the orthogonal subspace and passage to its radical quotient give a Lie equivalence when the stabilizer has trivial solvable radical. The restriction kernel has vanishing triple products, and every quotient skew endomorphism extends by an orthogonal projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalform-standardform-symm"),
                DeclarationHandle.Create(Prefix + "standardForm_symm"),
                H("standardForm symm"),
                StatementSource.FromAuthor(Disp(All(X("k"), Type, Instance(Call("Field", X("k")), All(X("n"), Type, Instance(Call("Fintype", X("n")), Instance(Call("DecidableEq", X("n")), Apply(Seq(Parenthesized(MatrixForm(X("n"))), Dot, Name("IsSymm")))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The bilinear form of the identity matrix is symmetric."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalform-skewadjoint-equiv-so"),
                DeclarationHandle.Create(Prefix + "skewAdjoint_equiv_so"),
                H("skewAdjoint equiv so"),
                StatementSource.FromAuthor(Disp(AlgebraContext(Instance(Call("FiniteDimensional", X("k"), X("V")), Instance(Call("IsAlgClosed", X("k")), Instance(Call("CharZero", X("k")), All(X("B"), Bilin, Hyp(Apply(Seq(X("B"), Dot, Name("IsSymm"))), Hyp(Apply(Seq(X("B"), Dot, Name("Nondegenerate"))), Nonempty(LieEquivalence(Call("skewAdjointLieSubalgebra", X("B")), So(Call("Fin", Apply(Qualified("Module", "finrank"), X("k"), X("V"))))))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Over an algebraically closed field of characteristic zero, a finite-dimensional nondegenerate symmetric form has the standard orthogonal Lie algebra of its dimension."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula content) =>Seq(Open, content, Close);
    private static Formula X(string name) =>F.Id(name);
    private static Formula Name(string name) =>Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) =>Seq(Name(owner), Dot, Name(name));
    private static Formula Apply(Formula f, params Formula[] args) =>new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>Apply(Name(name), args);
    private static Formula All(Formula x, Formula type, Formula body) =>Seq(Forall, Sp, Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Hyp(Formula hypothesis, Formula body) =>Imp(hypothesis, body);
    private static Formula Instance(Formula type, Formula body) =>Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Fn(Formula x, Formula body) =>Parenthesized(Seq(Name("fun"), Sp, x, Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) =>new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Val(Formula a) =>Call("val", a);
    private static Formula Type =>Name("Type");
    private static Formula Bilin =>Apply(Qualified("LinearMap", "BilinForm"), X("k"), X("V"));
    private static Formula Submodule =>Call("Submodule", X("k"), X("V"));
    private static Formula So(Formula n) =>Apply(Seq(Name("LieAlgebra"), Dot, Name("Orthogonal"), Dot, Name("so")), n, X("k"));
    private static Formula LieEquivalence(Formula a, Formula b) =>Call("LieEquiv", X("k"), a, b);
    private static Formula Nonempty(Formula t) =>Call("Nonempty", t);
    private static Formula AlgebraContext(Formula body) =>All(X("k"), Type, Instance(Call("Field", X("k")), All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", X("k"), X("V")), body)))));
    private static Formula Orth =>Apply(Seq(X("B"), Dot, Name("orthogonal")), X("W"));
    private static Formula Restrict =>Apply(Seq(X("B"), Dot, Name("restrict")), Orth);
    private static Formula Radical =>Apply(Qualified("LinearMap", "ker"), Restrict);
    private static Formula QuotientForm =>Apply(Seq(Name("LinearMap"), Dot, Name("IsRefl"), Dot, new Formula.Subscript(Name("liftQ"), D(2))), Restrict, Radical, Fn(X("x"), Fn(X("y"), Apply(Seq(X("hB"), Dot, Name("isRefl")), Val(X("x")), Val(X("y"))))));
    private static Formula FormContext(Formula body) =>AlgebraContext(All(X("B"), Bilin, All(X("W"), Submodule, All(X("hB"), Apply(Seq(X("B"), Dot, Name("IsSymm"))), body))));
    private static Formula MatrixForm(Formula n) =>Apply(Seq(Name("Matrix"), Dot, new Formula.Subscript(Name("toLinearMap"), D(2)), Apos), X("k"), Seq(D(1), Sp, Colon, Sp, Call("Matrix", n, n, X("k"))));
}

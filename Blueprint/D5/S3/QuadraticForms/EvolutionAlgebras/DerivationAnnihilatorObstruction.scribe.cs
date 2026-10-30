using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class DerivationAnnihilatorObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural squares and semisimple derivations.",
        H("Natural squares and semisimple derivations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("isevolutionalgebra"),
                DeclarationHandle.Create(Prefix + "IsEvolutionAlgebra"),
                H("IsEvolutionAlgebra"),
                StatementSource.FromAuthor(Disp(ProductContext(Eq(Call("IsEvolutionAlgebra", Mu), And(All(X("x"), X("V"), All(X("y"), X("V"), Eq(Apply(Mu, X("x"), X("y")), Apply(Mu, X("y"), X("x"))))), Some(Iota, Type, Some(X("b"), Basis(Iota, X("V")), Natural(X("b"), Iota)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Section 1.1, p. 3: “Let k be a field. A k-algebra A is called an evolution algebra if it admits a basis B = {eᵢ}ᵢ∈Λ, called a natural basis, such that eᵢeⱼ = 0 whenever i ≠ j. Evolution algebras are commutative, and in general they are neither associative nor power-associative.” Here the two conjuncts express commutativity and the natural basis property; no associativity or unit is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("derivations"),
                DeclarationHandle.Create(Prefix + "derivations"),
                H("derivations"),
                StatementSource.FromAuthor(Disp(ProductContext(Eq(Der, Seq(OpenBrace, X("D"), Sp, Colon, Sp, Apply(Qualified("Module", "End"), X("k"), X("V")), Sp, Mid, Sp, All(X("x"), X("V"), All(X("y"), X("V"), Eq(Apply(X("D"), Apply(Mu, X("x"), X("y"))), Add(Apply(Mu, Apply(X("D"), X("x")), X("y")), Apply(Mu, X("x"), Apply(X("D"), X("y"))))))), CloseBrace))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Der(A) consists of the linear maps D satisfying D(xy) = D(x)y + xD(y), with the commutator bracket. The displayed carrier determines the Lie subalgebra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("perfectness-semisimple-perfect"),
                DeclarationHandle.Create(Prefix + "semisimple_perfect"),
                H("semisimple perfect"),
                StatementSource.FromAuthor(Disp(All(X("k"), Type, Instance(Call("Field", X("k")), All(X("L"), Type, Instance(Call("LieRing", X("L")), Instance(Call("LieAlgebra", X("k"), X("L")), Instance(Apply(Qualified("LieAlgebra", "IsSemisimple"), X("k"), X("L")), Eq(Lie(Top(LieIdeal(X("L"))), Top(LieIdeal(X("L")))), Top(LieIdeal(X("L")))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A semisimple Lie algebra equals its derived ideal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("annihilator-square"),
                DeclarationHandle.Create(Prefix + "square"),
                H("square"),
                StatementSource.FromAuthor(Disp(ProductContext(Eq(Apply(Qualified("Annihilator", "square"), Mu), Apply(Qualified("Submodule", "span"), X("k"), Seq(OpenBrace, X("v"), Sp, Mid, Sp, Some(X("x"), X("V"), Some(X("y"), X("V"), Eq(Apply(Mu, X("x"), X("y")), X("v")))), CloseBrace)))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The square space is the span of all products."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("annihilator-semisimple-ann-or-perfect"),
                DeclarationHandle.Create(Prefix + "semisimple_ann_or_perfect"),
                H("semisimple ann or perfect"),
                StatementSource.FromAuthor(Disp(ProductContext(Hyp(All(X("x"), X("V"), All(X("y"), X("V"), Eq(Apply(Mu, X("x"), X("y")), Apply(Mu, X("y"), X("x"))))), Instance(Call("FiniteDimensional", X("k"), X("V")), Instance(Apply(Qualified("LieAlgebra", "IsSemisimple"), X("k"), Der), Or(Eq(Apply(Qualified("LinearMap", "ker"), Mu), Name("bot")), Eq(Apply(Qualified("Annihilator", "square"), Mu), Name("top"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a finite-dimensional commutative bilinear algebra with semisimple derivations, either the annihilator is zero or every vector belongs to the square space. A nonzero annihilator together with a proper square space produces an abelian ideal or an annihilator action of trace one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("annihilator-semisimple-natural-squares-ne-zero"),
                DeclarationHandle.Create(Prefix + "semisimple_natural_squares_ne_zero"),
                H("semisimple natural squares ne zero"),
                StatementSource.FromAuthor(Disp(ProductContext(Hyp(All(X("x"), X("V"), All(X("y"), X("V"), Eq(Apply(Mu, X("x"), X("y")), Apply(Mu, X("y"), X("x"))))), All(Iota, Type, All(X("b"), Basis(Iota, X("V")), Hyp(Natural(X("b"), Iota), Instance(Call("FiniteDimensional", X("k"), X("V")), Instance(Apply(Qualified("LieAlgebra", "IsSemisimple"), X("k"), Der), All(X("i"), Iota, Ne(Apply(Mu, Apply(X("b"), X("i")), Apply(X("b"), X("i"))), D(0)))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every vector of a natural basis has nonzero square. A zero square makes the square-map singular and supplies a nonzero annihilator vector, contradicting the preceding dichotomy."))),
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
    private static Formula Eq(Formula a, Formula b) =>new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Ne(Formula a, Formula b) =>new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula LMap(Formula a, Formula b) =>Call("LinearMap", X("k"), a, b);
    private static Formula Type =>Name("Type");
    private static Formula Product =>LMap(X("V"), LMap(X("V"), X("V")));
    private static Formula Der =>Call("derivations", Mu);
    private static Formula LieIdeal(Formula l) =>Call("LieIdeal", X("k"), l);
    private static Formula Top(Formula type) =>Seq(Name("top"), Sp, Colon, Sp, type);
    private static Formula Lie(Formula a, Formula b) =>Apply(Qualified("Bracket", "bracket"), a, b);
    private static Formula AlgebraContext(Formula body) =>All(X("k"), Type, Instance(Call("Field", X("k")), All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", X("k"), X("V")), body)))));
    private static Formula ProductContext(Formula body) =>AlgebraContext(All(Mu, Product, body));
    private static Formula Basis(Formula index, Formula v) =>Apply(Qualified("Module", "Basis"), index, X("k"), v);
    private static Formula Natural(Formula b, Formula index) =>All(X("i"), index, All(X("j"), index, Imp(Ne(X("i"), X("j")), Eq(Apply(Mu, Apply(b, X("i")), Apply(b, X("j"))), D(0)))));
}

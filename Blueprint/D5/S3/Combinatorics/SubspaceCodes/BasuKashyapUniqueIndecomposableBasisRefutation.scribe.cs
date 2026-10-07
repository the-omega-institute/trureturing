using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class BasuKashyapUniqueIndecomposableBasisRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/basu2019latticesubspacecodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unique indecomposable basis need not imply intersection closure.",
        H("A Unique Indecomposable Basis Without Intersection Closure"),
        Blocks(
            Node("bk-distance", "Subspace distance", "dS", DistanceFormula(),
                "On page 2 the subspace distance is d_S(X,Y) = dim X + dim Y − 2 dim(X ∩ Y). Dimensions are Module.finrank; the casts to integers precede subtraction. The ambient space in the conjecture is Fin n → F.", true),
            Node("bk-linear-code", "Linear subspace codes", "LinearCode", CodeFormula(),
                "Pages 4–5, Definition 1 (TeX label L): “A subset 𝒰 ⊆ ℙ_q(n), with {0} ∈ 𝒰, is a linear subspace code if there exists a function ⊞ : 𝒰 × 𝒰 → 𝒰 such that: (i) (𝒰, ⊞) is an abelian group; (ii) the identity element of (𝒰, ⊞) is {0}; (iii) X ⊞ X = {0} for every group element X ∈ 𝒰; (iv) the addition operation ⊞ is isometric, i.e., d_S(X ⊞ Y₁, X ⊞ Y₂) = d_S(Y₁, Y₂) for all X, Y₁, Y₂ ∈ 𝒰.” LinearCode records U, its bottom membership, and the operation on the subtype, followed by exactly these laws. The identity is the subtype pair formed from bottom and botMem.", true),
            Node("bk-zero", "The identity codeword", "codeZero", ZeroFormula(),
                "The identity codeword is the zero submodule equipped with its membership proof.", false),
            Node("bk-indecomposable", "Indecomposable codewords", "Indecomposable", IndecomposableFormula(),
                "Page 19, Definition 11 (TeX label 9): “A codeword Y ≠ {0} of a linear subspace code 𝒰 is said to be indecomposable if Y cannot be expressed as Y = Y₁ ⊞ Y₂ for any Y₁,Y₂ ∈ 𝒰 with dim Y₁, dim Y₂ < dim Y.” The two strict inequalities concern ambient subspace dimensions; the summation uses L.op.", true),
            Node("bk-basis", "An unordered basis", "IsBasis", BasisFormula(),
                "Section 6, page 22: “We observed earlier that the indecomposable codewords in a linear subspace code constitute a basis for the vector space over 𝔽₂ formed by the code (Remark 5). We refer to such a basis as an indecomposable basis.” A basis is a finite subset S of the subtype L.U such that every codeword has exactly one representing finite subset T of S. Finite sums use Finset.fold with L.op, identity L.codeZero and id, with associative and commutative instances supplied by L.assoc and L.comm; the empty sum is L.codeZero. This is the 𝔽₂-space formed by the code operation. It is not an ordered list or an ambient F-basis.", true),
            Node("bk-indecomposable-basis", "An indecomposable basis", "IsIndecomposableBasis", IndecomposableBasisFormula(),
                "Section 6, page 22: “We refer to such a basis as an indecomposable basis.” Every member of this basis is indecomposable, and the basis is an unordered finite subset of codewords.", true),
            Node("bk-claim", "Conjecture 6.1", "claim", ClaimFormula(),
                "Page 23, Conjecture 6.1: “A linear code 𝒰 in ℙ_q(n) has a unique indecomposable basis if and only if 𝒰 is closed under intersection.” F ranges over finite fields in Type, n over natural numbers, and L over all subsets of Submodule F (Fin n → F) with every operation satisfying the four defining axioms. Uniqueness is uniqueness of an unordered finite subset of codewords, with basis and indecomposability relative to that same operation. InfClosed L.U expresses closure under the infimum of actual submodules: page 15, Definition 9 (TeX label 8), “A linear code 𝒰 ⊆ ℙ_q(n) with the property that X ∩ Y ∈ 𝒰 whenever X, Y ∈ 𝒰 is said to be a linear code closed under intersection.”", true),
            Describe.Lean(DescribeId.Create("bk-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation by a Klein family"), StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("For every finite field, split the coordinates into three disjoint blocks I,P,Q of dimensions i,a,b with 0 < i < a and i < b. The subspaces A = I ⊕ P, B = I ⊕ Q and C = P ⊕ Q, together with zero, form a linear subspace code under Klein addition. Their intersections are I,P,Q; their dimensions are i+a,i+b,a+b. Translation preserves the literal integer subspace distance.")),
                    Paragraph(Text("Exactly A and B are indecomposable: C = A ⊞ B has two strictly smaller summands, whereas every decomposition of A or B includes a summand of at least its dimension. The four distinct subset sums of {A,B} exhaust the code, and every indecomposable basis must contain both. The nonzero intersection I is outside the code. The universal conjecture fails at F = ZMod 2, i = 1, a = b = 2, n = 5.")),
                    Paragraph(Text("Remark 5 on page 21 assumes intersection closure when asserting that the indecomposables form a basis. That qualifier is omitted in the Section 6 recap. The source's intersection-closed direction remains intact, as do its proved lattice statements under that hypothesis; the separate Braun–Etzion–Vardy cardinality conjecture is unaffected."))), DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Member(Formula value, string field) => Seq(value, Dot, Named(field));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] arguments) => DefinitionDsl.Call(name, arguments);
    private static Formula Apply(Formula function, params Formula[] arguments) => Seq(function, Parenthesized(Arguments(arguments)));
    private static Formula Arguments(Formula[] arguments)
    {
        var items = new System.Collections.Generic.List<Formula>();
        for (var j = 0; j < arguments.Length; ++j)
        {
            if (j > 0) items.Add(Comma);
            items.Add(arguments[j]);
        }
        return Seq([.. items]);
    }
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Unique(string name, Formula domain, Formula body) => Seq(Exists, Bang, Parenthesized(Seq(F.Id(name), Colon, domain)), Comma, Sp, body);
    private static Formula And(params Formula[] clauses)
    {
        Formula body = Parenthesized(clauses[^1]);
        for (var j = clauses.Length - 2; j >= 0; --j)
            body = new Formula.Logic(Parenthesized(clauses[j]), FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Mem(Formula x, Formula s) => Rel(x, FormulaRelationOperator.MemberOf, s);
    private static Formula Rank(Formula x) => Call("finrank", F.Id("F"), x);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Op(Formula x, Formula y) => Apply(Member(F.Id("L"), "op"), x, y);
    private static Formula CodeSet() => Member(F.Id("L"), "U");
    private static Formula Bot() => Qualified("Bot", "bot");
    private static Formula Inf(Formula x, Formula y) => Apply(Qualified("Min", "min"), x, y);
    private static Formula Instances(Formula body) => Seq(
        OpenBracket, Call("Field", F.Id("F")), CloseBracket, Sp,
        OpenBracket, Call("AddCommGroup", F.Id("V")), CloseBracket, Sp,
        OpenBracket, Call("Module", F.Id("F"), F.Id("V")), CloseBracket, Comma, Sp, body);
    private static Formula Ambient(Formula body) => All("F", Named("Type"), All("V", Named("Type"), Instances(body)));
    private static Formula WithCode(Formula body) => Ambient(All("L", Call("LinearCode", F.Id("F"), F.Id("V")), body));
    private static Formula WithSet(Formula body) => WithCode(All("S", Call("Finset", CodeSet()), body));
    private static Formula Pred(string field, Formula x) => Apply(Member(F.Id("L"), field), x);
    private static Formula ZeroFormula() => Disp(WithCode(Equal(Member(F.Id("L"), "codeZero"),
        Seq(Langle, Bot(), Comma, Member(F.Id("L"), "botMem"), Rangle))));

    private static Formula DistanceFormula()
    {
        var x = F.Id("X"); var y = F.Id("Y");
        Formula integerRank(Formula s) => Seq(Parenthesized(Seq(Rank(s), Colon, Named("Int"))));
        return Disp(Ambient(All("X", Call("Submodule", F.Id("F"), F.Id("V")),
            All("Y", Call("Submodule", F.Id("F"), F.Id("V")),
            Equal(Call("dS", x, y), Subtract(Add(integerRank(x), integerRank(y)), Multiply(Num(2), integerRank(Inf(x, y)))))))));
    }
    private static Formula CodeFormula()
    {
        var l = F.Id("L"); var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var zero = Seq(Langle, Bot(), Comma, Member(l, "botMem"), Rangle);
        Formula typed(string field, Formula type) => Parenthesized(Seq(Member(l, field), Colon, type));
        Formula xy(Formula body) => All("x", CodeSet(), All("y", CodeSet(), body));
        var fields = new Formula[] {
            typed("U", Call("Set", Call("Submodule", F.Id("F"), F.Id("V")))),
            typed("botMem", Mem(Bot(), CodeSet())),
            typed("op", Arrow(CodeSet(), Arrow(CodeSet(), CodeSet()))),
            typed("assoc", xy(All("z", CodeSet(), Equal(Op(Op(x,y),z), Op(x,Op(y,z)))))),
            typed("comm", xy(Equal(Op(x,y), Op(y,x)))),
            typed("leftId", All("x", CodeSet(), Equal(Op(zero,x),x))),
            typed("rightId", All("x", CodeSet(), Equal(Op(x,zero),x))),
            typed("inverse", All("x", CodeSet(), Ex("y", CodeSet(), And(Equal(Op(x,y),zero), Equal(Op(y,x),zero))))),
            typed("self", All("x", CodeSet(), Equal(Op(x,x),zero))),
            typed("isometry", xy(All("z", CodeSet(), Equal(Call("dS",Val(Op(x,y)),Val(Op(x,z))), Call("dS",Val(y),Val(z))))))
        };
        return Disp(WithCode(Aligned(fields)));
    }
    private static Formula Aligned(Formula[] rows)
    {
        var items = new System.Collections.Generic.List<Formula> { Begin, Grp(F.Id("aligned")) };
        for (var j = 0; j < rows.Length; ++j) { if (j > 0) items.Add(RowBreak); items.Add(rows[j]); }
        items.Add(End); items.Add(Grp(F.Id("aligned")));
        return Seq([.. items]);
    }
    private static Formula IndecomposableFormula()
    {
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var decomposition = Ex("y",CodeSet(),Ex("z",CodeSet(),And(Equal(x,Op(y,z)),
            Rel(Rank(Val(y)), FormulaRelationOperator.LessThan, Rank(Val(x))),
            Rel(Rank(Val(z)), FormulaRelationOperator.LessThan, Rank(Val(x))))));
        return Disp(WithCode(All("x",CodeSet(), Iff(Pred("Indecomposable",x),
            And(NotEqual(Val(x),Bot()),new Formula.Not(Parenthesized(decomposition)))))));
    }
    private static Formula BasisFormula() => Disp(WithSet(Iff(Pred("IsBasis",F.Id("S")),
        All("x",CodeSet(),Unique("T",Call("Finset",CodeSet()),And(
            Rel(F.Id("T"),FormulaRelationOperator.SubsetOf,F.Id("S")),Equal(Apply(Qualified("Finset","fold"),Member(F.Id("L"),"op"),Member(F.Id("L"),"codeZero"),Named("id"),F.Id("T")),F.Id("x"))))))));
    private static Formula IndecomposableBasisFormula() => Disp(WithSet(Iff(Pred("IsIndecomposableBasis",F.Id("S")),
        And(Pred("IsBasis",F.Id("S")),All("x",CodeSet(),Implies(Mem(F.Id("x"),F.Id("S")),Pred("Indecomposable",F.Id("x"))))))));
    private static Formula ClaimFormula() => Disp(Iff(Named("claim"),All("F",Named("Type"),Seq(
        OpenBracket,Call("Field",F.Id("F")),CloseBracket,Sp,
        OpenBracket,Call("Fintype",F.Id("F")),CloseBracket,Comma,Sp,
        All("n",Named("Nat"),All("L",Call("LinearCode",F.Id("F"),Arrow(Call("Fin",F.Id("n")),F.Id("F"))),
            Iff(Unique("S",Call("Finset",CodeSet()),Pred("IsIndecomposableBasis",F.Id("S"))),Call("InfClosed",CodeSet()))))))));
}

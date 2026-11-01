using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class ReversibleFourByFourNonuniquenessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/HilbertOperators/blecher2025commutativity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weighted anticommuting algebra of four-by-four complex matrices disproves unitary uniqueness of reversible algebras.",
        H("Reversible four-by-four algebras need not be unitarily equivalent"),
        Blocks(
            Definition("is-matrix-algebra", "IsMatrixAlgebra", "Multiplicative closure",
                MatrixAlgebraFormula(), AssessedProvenance.FromLiterature(Source),
                "A complex subspace b of the four-by-four matrices is a matrix algebra when it is closed under multiplication. "
                    + "No multiplicative identity is required. This is the finite-matrix setting of the concrete operator algebras "
                    + "in 3commfarx.tex, lines 140–145; the norm is inherited from the ambient operators."),
            Definition("is-noncommutative", "IsNoncommutative", "A noncommuting pair",
                NoncommutativeFormula(), AssessedProvenance.FromLiterature(Source),
                "Noncommutativity means that b contains two matrices x and y for which xy differs from yx. "
                    + "The same criterion appears for the CAR example in 3commfarx.tex, line 661."),
            Definition("is-reversible", "IsReversible", "Reversed multiplication with all matrix norms preserved",
                ReversibleFormula(), AssessedProvenance.FromLiterature(Source),
                "There must be a positive natural m and a complex-linear map ρ from the whole ambient four-by-four "
                    + "matrix space to the m-by-m matrices. On b the map reverses multiplication, and entrywise application "
                    + "preserves the Euclidean operator norm of every Matrix.comp assembly of an n-by-n family of "
                    + "four-by-four blocks, for every natural n. "
                    + "DFunLike.coe explicitly treats ρ as a function. The condition on block entries is an implication. "
                    + "Reversibility in 3commfarx.tex, line 145, means that reversed multiplication with the same matrix "
                    + "norms is again an abstract operator algebra. The displayed finite-matrix representation is a "
                    + "sufficient condition for that notion: the restriction of ρ to b is a completely isometric "
                    + "antihomomorphism. It specifies a finite-dimensional representation and an ambient linear map, "
                    + "neither of which is required in the source's general definition."),
            Definition("car-algebra", "carAlgebra", "The CAR algebra in four dimensions",
                CarAlgebraFormula(), AssessedProvenance.FromLiterature(Source),
                "Matrix.single i j 1 is the matrix unit with its only nonzero entry at row i, column j. "
                    + "Indices start at zero, so u = e₀₂ + e₁₃ and v = e₀₁ − e₂₃ are precisely the matrices "
                    + "U = e₁₃ + e₂₄ and V = e₁₂ − e₃₄ of 3commfarx.tex, lines 647–653. "
                    + "The subspace is their complex span together with their product uv. "
                    + "The displayed local definitions bind u and v before taking that span."),
            Definition("unitarily-equivalent", "UnitarilyEquivalent", "Equality under unitary conjugation",
                UnitarilyEquivalentFormula(), AssessedProvenance.FromLiterature(Source),
                "There is a unitary matrix q such that x belongs to b exactly when qᴴxq belongs to c, for every "
                    + "ambient matrix x. The quantified type consists of the elements of the unitary group. "
                    + "Subtype.val explicitly extracts the matrix from q, and star is its adjoint. "
                    + "Thus conjugation carries b onto c, rather than merely into c. This is unitary equivalence as used "
                    + "in the conjecture in 3commfarx.tex, line 684; replacing q by its adjoint reverses the orientation."),
            Definition("claim", "claim", "The proposed unitary uniqueness",
                ClaimFormula(), AssessedProvenance.FromRepo(Source),
                "Every multiplicatively closed, noncommutative complex subspace b of the four-by-four matrices "
                    + "satisfying the displayed reversibility condition would be unitarily equivalent to carAlgebra. "
                    + "This is the finite-matrix representation reading of the conjecture in 3commfarx.tex, line 684. "
                    + "The source's conjecture implies this assertion because this reversibility condition implies "
                    + "the source's abstract reversibility."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A weighted algebra separates the unitary classes"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For complex t, a, b and c, write F(t,a,b,c) for the matrix whose only possibly nonzero entries "
                            + "are (0,1) = tb, (0,2) = ta, (0,3) = c, (1,3) = a and (2,3) = −b. "
                            + "Put U₂ = F(2,1,0,0), V₂ = F(2,0,1,0), W = F(2,0,0,1) = e₀₃, "
                            + "and B = spanℂ{U₂,V₂,W}. Entrywise expansion gives "
                            + "aF(t,1,0,0) + bF(t,0,1,0) + cF(t,0,0,1) = F(t,a,b,c). "
                            + "Consequently the elements of B are exactly F(2,a,b,c).")),
                    Paragraph(Text(
                        "Multiplication gives F(t,a,b,c)F(t,d,e,f) = F(t,0,0,t(bd − ae)). "
                            + "The matrices u and v defining carAlgebra are F(1,1,0,0) and F(1,0,1,0); "
                            + "their product is −W. Changing the sign of the third span coefficient shows that "
                            + "the elements of carAlgebra are exactly F(1,a,b,c).")),
                    Paragraph(Text(
                        "The product identity first proves that B is closed under multiplication, since every product "
                            + "is a scalar multiple of W. Interchanging the two factors negates bd − ae, so xy = −yx "
                            + "for every x and y in B. Moreover U₂V₂ = −2W and V₂U₂ = 2W. Their (0,3) entries "
                            + "are −2 and 2, proving noncommutativity. For reversibility take m = 4 and ρ = −id "
                            + "on the ambient matrix space. Anticommutation gives ρ(yx) = −yx = xy = ρ(x)ρ(y). "
                            + "Applying ρ to every block negates the assembled matrix, so its norm is unchanged "
                            + "at every natural block size.")),
                    Paragraph(Text(
                        "For a unitary q let T(X) = qᴴXq, where Xᴴ denotes the adjoint. The current proof expresses T "
                            + "as Unitary.conjStarAlgAut and applies Matrix.trace_units_conj' after transporting products, "
                            + "adjoints and squares. Thus Δ(X) = 2tr((XXᴴ)²) − tr(XXᴴ)² is invariant under T. "
                            + "Direct expansion gives Δ(F(1,a,b,0)) = 0 for all complex a and b, "
                            + "whereas Δ(U₂) = 9.")),
                    Paragraph(Text(
                        "Suppose T carries B into carAlgebra. Write T(U₂) = F(1,a,b,c) and T(V₂) = F(1,d,e,f). "
                            + "Since W = (1/2)V₂U₂, multiplicativity and complex linearity give "
                            + "T(W) = ((ea − db)/2)W. Denote this coefficient by t. It is nonzero: otherwise "
                            + "injectivity of T would give W = 0, contradicting its (0,3) entry, which is one.")),
                    Paragraph(Text(
                        "Next write T(U₂) = F(1,a,b,c) again. The equality tr(WᴴU₂) = 0 is preserved by T, "
                            + "so tr(T(W)ᴴT(U₂)) = 0. Substituting T(W) = tW and expanding the trace gives "
                            + "conj(t)c = 0. Since t is nonzero, c = 0. Thus T(U₂) = F(1,a,b,0).")),
                    Paragraph(Text(
                        "A unitary equivalence between B and carAlgebra would give the inclusion just used. "
                            + "Invariance of Δ would then identify Δ(F(1,a,b,0)) with Δ(U₂), forcing 0 = 9. "
                            + "Hence those two subspaces are not unitarily equivalent. Finally, applying claim to B, "
                            + "with its multiplicative closure, noncommutativity and reversibility established above, "
                            + "would supply exactly that impossible equivalence. Therefore claim is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("blecher-2025-reversible-four-by-four-nonuniqueness"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula MatrixAlgebraFormula() => All("b", Subspace(), Equivalence(
        LocalCall("IsMatrixAlgebra", X("b")), All("x", FourMatrix(), Arrow(Member(X("x"), X("b")),
            All("y", FourMatrix(), Arrow(Member(X("y"), X("b")), Member(Multiply(X("x"), X("y")), X("b"))))))));

    private static Formula NoncommutativeFormula() => All("b", Subspace(), Equivalence(
        LocalCall("IsNoncommutative", X("b")), Some("x", FourMatrix(), Conjunction(Member(X("x"), X("b")),
            Some("y", FourMatrix(), Conjunction(Member(X("y"), X("b")),
                NotEqual(Multiply(X("x"), X("y")), Multiply(X("y"), X("x")))))))));

    private static Formula ReversibleFormula()
    {
        Formula map = Typed(At(Qualified("DFunLike", "coe"), X("ρ")),
            Arrow(FourMatrix(), MatrixType(FinOf(X("m")))));
        Formula multiplicative = All("x", FourMatrix(), Arrow(Member(X("x"), X("b")),
            All("y", FourMatrix(), Arrow(Member(X("y"), X("b")),
                Equal(At(map, Multiply(X("y"), X("x"))), Multiply(At(map, X("x")), At(map, X("y"))))))));
        Formula entries = All("i", FinOf(X("n")), All("j", FinOf(X("n")),
            Member(At(X("x"), X("i"), X("j")), X("b"))));
        Formula mapped = LambdaOf("i", FinOf(X("n")), LambdaOf("j", FinOf(X("n")),
            At(map, At(X("x"), X("i"), X("j")))));
        Formula mappedMatrix = At(Qualified("Matrix", "comp"), FinOf(X("n")), FinOf(X("n")),
            FinOf(X("m")), FinOf(X("m")), Complexes(), mapped);
        Formula originalMatrix = At(Qualified("Matrix", "comp"), FinOf(X("n")), FinOf(X("n")),
            FinOf(Nat(4)), FinOf(Nat(4)), Complexes(), X("x"));
        Formula isometric = All("n", Naturals(), All("x", BlocksType(X("n"), Nat(4)), Arrow(entries,
            Equal(new Formula.Norm(mappedMatrix), new Formula.Norm(originalMatrix)))));
        return All("b", Subspace(), Equivalence(LocalCall("IsReversible", X("b")), Some("m", Naturals(),
            Conjunction(Less(Nat(0), X("m")), Some("ρ", LinearMapType(FourMatrix(), MatrixType(FinOf(X("m")))),
                Conjunction(multiplicative, isometric))))));
    }

    private static Formula CarAlgebraFormula()
    {
        Formula u = Add(Single(0, 2), Single(1, 3));
        Formula v = Subtract(Single(0, 1), Single(2, 3));
        Formula span = At(Qualified("Submodule", "span"), Complexes(),
            new Formula.SetLiteral([X("u"), X("v"), Multiply(X("u"), X("v"))]));
        return Equal(Typed(Local("carAlgebra"), Subspace()),
            LetIn("u", FourMatrix(), u, LetIn("v", FourMatrix(), v, span)));
    }

    private static Formula UnitarilyEquivalentFormula()
    {
        Formula q = Typed(At(Qualified("Subtype", "val"), X("q")), FourMatrix());
        Formula image = Multiply(Multiply(At(Qualified("star"), q), X("x")), q);
        Formula unitaries = At(Qualified("Matrix", "unitaryGroup"), FinOf(Nat(4)), Complexes());
        Formula body = Some("q", At(Qualified("CoeSort", "coe"), unitaries),
            All("x", FourMatrix(), Equivalence(Member(X("x"), X("b")), Member(image, X("c")))));
        return All("b", Subspace(), All("c", Subspace(),
            Equivalence(LocalCall("UnitarilyEquivalent", X("b"), X("c")), body)));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"), All("b", Subspace(),
        Arrow(LocalCall("IsMatrixAlgebra", X("b")), Arrow(LocalCall("IsNoncommutative", X("b")),
            Arrow(LocalCall("IsReversible", X("b")), LocalCall("UnitarilyEquivalent", X("b"), Local("carAlgebra")))))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat(byte value) => Typed(D(value), Naturals());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula MatrixType(Formula index) => At(Qualified("Matrix"), index, index, Complexes());
    private static Formula FourMatrix() => MatrixType(FinOf(Nat(4)));
    private static Formula Subspace() => At(Qualified("Submodule"), Complexes(), FourMatrix());
    private static Formula BlocksType(Formula n, Formula k) => Arrow(FinOf(n), Arrow(FinOf(n), MatrixType(FinOf(k))));
    private static Formula LinearMapType(Formula domain, Formula codomain) => Seq(Parenthesized(domain), Sp,
        new Formula.Subscript(To, F.Id("l")), OpenBracket, Complexes(), CloseBracket, Sp, Parenthesized(codomain));
    private static Formula Single(byte i, byte j) => At(Qualified("Matrix", "single"),
        Typed(D(i), FinOf(Nat(4))), Typed(D(j), FinOf(Nat(4))), Typed(D(1), Complexes()));
    private static Formula X(string name) => name == "ρ" ? Rho : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "HilbertOperators", "ReversibleFourByFourNonuniqueness", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula LetIn(string name, Formula type, Formula value, Formula body) => Parenthesized(
        Seq(Qualified("let"), Sp, Typed(X(name), type), Sp, Eq, Sp, Parenthesized(value), Semi, Sp, body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Conjunction(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}

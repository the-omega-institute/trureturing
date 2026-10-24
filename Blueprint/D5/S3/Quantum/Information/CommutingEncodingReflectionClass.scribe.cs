using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CommutingEncodingReflectionClassDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/CommutingEncodingReflectionClass";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/pauwelsguhne2026measurementbases");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting product unitaries and commuting local reflections encode exactly the same qubit states.",
        H("Commuting encodings and local reflections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("commuting-product-encoding"),
                DeclarationHandle.Create(Module + ".IsCommutingProductEncoding"),
                H("A commuting product encoding"),
                StatementSource.FromAuthor(Disp(ProductDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n qubits, U has exactly 2ⁿ labels and one unitary two-by-two factor at each site. "
                    + "The complete tensor operators commute pairwise, and their images of ψ are orthonormal. "
                    + "Thus they form a basis of the 2ⁿ-dimensional state space. The local factors themselves "
                    + "are not required to commute. This combines the local-encoding definition in main.tex, "
                    + "lines 328–340, with the commuting families discussed in lines 374–384. "
                    + "The predicate imposes no separate normalization hypothesis on ψ."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("commuting-reflection-encoding"),
                DeclarationHandle.Create(Module + ".IsCommutingReflectionEncoding"),
                H("A commuting reflection encoding"),
                StatementSource.FromAuthor(Disp(ReflectionDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A commuting reflection encoding is a commuting product encoding whose every "
                    + "local factor is Hermitian and squares to the identity matrix. This is the "
                    + "commuting-reflection case of the encoder-structures definition in main.tex, "
                    + "lines 357–368. The tensor operators commute even when some of their factors anticommute."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Equality of the two encoding classes"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive natural number n and every normalized n-qubit vector ψ, "
                    + "existence of a commuting product encoding is equivalent to existence of a "
                    + "commuting reflection encoding. Section VI, main.tex lines 1539–1546, asks for "
                    + "the state class defined by commuting encoders with non-Hermitian local factors. "
                    + "The displayed assertion specifies equality with the reflection class. "
                    + "The source characterizes the reflection class in lines 542–560."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Reflection replacements for commuting product encodings"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix n ≥ 1, ψ and a commuting product encoding U. For two labels a and b, "
                        + "the tensor products of the local products U(a,j)U(b,j) and U(b,j)U(a,j) "
                        + "are equal and nonzero. Choose a nonzero entry of this tensor matrix and "
                        + "vary only its row and column coordinates at site j. Cancelling the product "
                        + "of the other entries shows that the two local products are proportional. "
                        + "Their nonzero two-by-two determinants give c² = 1 for the proportionality "
                        + "scalar. Consequently each pair of local factors either commutes or anticommutes.")),
                    Paragraph(Text(
                        "At each site choose a unitary V(j) as follows. If a nonscalar factor has "
                        + "nonzero trace, anticommutation with an invertible factor would negate its "
                        + "trace under conjugation, which is impossible. All factors therefore commute "
                        + "with it. Its two eigenvalues are distinct, so its unitary eigenbasis makes "
                        + "every factor diagonal. Otherwise each nonscalar factor is traceless. Its "
                        + "two unit-modulus eigenvalues are opposites, so it is a unit-modulus scalar "
                        + "times a Hermitian involution; scalar factors have the same form with the "
                        + "identity involution. Cancelling these phases preserves all commutation signs. "
                        + "Send a nonscalar involution to ±Z. If all involutions commute with Z, they "
                        + "also commute or anticommute with X. Otherwise a diagonal unitary fixing Z "
                        + "sends an anticommuting involution to X, and the signs with this pair determine "
                        + "all remaining factors. The four possibilities are scalar multiples of I, X, "
                        + "Y and Z. If all factors are scalar, the identity change of basis suffices.")),
                    Paragraph(Text(
                        "Put A(a,j) = V(j)U(a,j)V(j)ᴴ. Expand each tensor operator in Pauli words "
                        + "using its trace coefficients. Represent a Pauli letter by its two binary "
                        + "translation and phase coordinates, and let S be the binary linear span of "
                        + "the symbols of every word with a nonzero coefficient in any such expansion. "
                        + "At a diagonal site only I and Z can have nonzero trace coefficients. At a "
                        + "Pauli site only the letter proportional to A(a,j) can occur. Hence for "
                        + "any two words occurring in the expansions, their local Pauli commutation "
                        + "signs are exactly the signs of the corresponding local A factors. The "
                        + "complete A operators commute and their products are nonzero, so the product "
                        + "of these signs is one. Their binary symplectic pairing is therefore zero. "
                        + "Bilinearity makes S isotropic, and every tensor operator lies in the complex "
                        + "span of the Pauli words with symbol in S.")),
                    Paragraph(Text(
                        "Extend S to an inclusion-maximal isotropic subspace L in the finite binary "
                        + "symplectic space. A vector orthogonal to L could be adjoined while retaining "
                        + "isotropy, since the form is alternating. Maximality therefore gives L = L⊥. "
                        + "Nondegeneracy and the ambient dimension 2n imply dim L = n. Choose a basis "
                        + "of L and Pauli-word representatives of its basis vectors. These representatives "
                        + "are commuting involutions. Their products, indexed by binary strings a, "
                        + "define matrices H(a) with H(a+b) = H(a)H(b). Each H(a) is a unit-modulus "
                        + "phase times a Pauli word, and its symbol is the basis-coordinate image of a. "
                        + "Thus H(0) is the identity and every other H(a) has trace zero. Unitarity "
                        + "and H(a)² = I make H(a) Hermitian. Conversely every Pauli word whose symbol "
                        + "lies in L is a nonzero scalar multiple of one H(a).")),
                    Paragraph(Text(
                        "A Hermitian phase multiple of a nonzero Hermitian Pauli word has real "
                        + "phase, hence phase ±1. Absorb this sign into site zero, which exists because "
                        + "n ≥ 1. This expresses each H(a) as a tensor product of local Hermitian "
                        + "involutions R(a,j), with no change to its multiplication or trace identities.")),
                    Paragraph(Text(
                        "For binary strings a and x, let χ(a,x) = ∏ⱼ(−1)^((a(j)).val (x(j)).val) "
                        + "in the complex numbers. Form P(x) = ∑ₐ χ(a,x)H(a). Translation of the "
                        + "summation index gives H(a)P(x) = χ(a,x)P(x). The trace identities give "
                        + "tr P(x) = 2ⁿ, so P(x) has a nonzero column. Choose such a column v(x) and "
                        + "normalize it by multiplying by the inverse of the complex inclusion of "
                        + "its real norm. Distinct x and y differ at a site j; the Hermitian operator "
                        + "H(eⱼ) then has opposite eigenvalues on the two normalized columns, making "
                        + "them orthogonal. These columns form a unitary matrix F satisfying "
                        + "FᴴH(a)F = diagonal(χ(a,·)). Since every Pauli word with symbol in L "
                        + "lies in the span of the H(a), conjugation by F diagonalizes all of them "
                        + "and therefore all tensor operators formed from A. Write their diagonals "
                        + "as eig(a,x). Unitarity gives star(eig(a,x))eig(a,x) = 1.")),
                    Paragraph(Text(
                        "Conjugating the original encoding by the tensor product of V(j) preserves "
                        + "unitarity, commutation and inner products. Write its state in the F basis "
                        + "as c = Fᴴ(tensorOp(V)ψ). Identify the 2ⁿ labels with binary strings and "
                        + "form the square matrix M(x,a) = c(x)eig(a,x). The encoding's orthonormality "
                        + "gives MᴴM = I, hence MMᴴ = I. Each diagonal row equation, together with "
                        + "the unit modulus of eig(a,x), gives (↑(Fintype.card (Fin n → Fin 2)) : ℂ) "
                        + "star(c(x))c(x) = 1. Here the cardinality is cast from the natural numbers "
                        + "to the complex numbers. Since that cardinality is 2ⁿ, every squared "
                        + "amplitude is 1/(2ⁿ : ℂ).")),
                    Paragraph(Text(
                        "The operators tensorOp(R(a)) act on these flat amplitudes by the real "
                        + "signs χ(a,x). Their pairwise overlap is therefore the sum of χ(a,x)χ(b,x) "
                        + "divided by (2ⁿ : ℂ). A binary additive character sums to its domain's "
                        + "cardinality when trivial and to zero otherwise. This product character "
                        + "is trivial exactly when a = b, as evaluation on each coordinate string "
                        + "shows. Its sum is consequently (2ⁿ : ℂ) for equal labels and zero otherwise. "
                        + "The R operators therefore give an orthonormal orbit. Their diagonal forms "
                        + "commute, and each local Hermitian involution is unitary. Relabelling by "
                        + "Fin (2ⁿ) gives a commuting reflection encoding of tensorOp(V)ψ.")),
                    Paragraph(Text(
                        "Finally conjugate its local factors by V(j)ᴴ. Unitary conjugation preserves "
                        + "Hermitian involutions and the encoding conditions, and the inverse tensor "
                        + "unitary returns the state to ψ. This proves the forward implication. "
                        + "For the reverse implication retain the same factors and discard the "
                        + "additional Hermitian and involution conditions. The forward construction "
                        + "already obtains normalization from the orthonormal orbit; it does not "
                        + "need the separate unit-vector hypothesis in the displayed statement."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pauwels-guhne-2026-commuting-encoding-reflection-class"),
                    ResolutionKind.Proved)))));

    private static Formula ProductDefinition() => EncodingBinders(Equal(
        LocalCall("IsCommutingProductEncoding", Psi, V("U")), Parenthesized(ProductBody())));

    private static Formula ProductBody() => And(
        All("a", Labels, All("j", Sites, Member(Apply(V("U"), V("a"), V("j")), QubitUnitaries))),
        And(All("a", Labels, All("b", Labels, Equal(
                Multiply(Tensor(Apply(V("U"), V("a"))), Tensor(Apply(V("U"), V("b")))),
                Multiply(Tensor(Apply(V("U"), V("b"))), Tensor(Apply(V("U"), V("a"))))))),
            All("a", Labels, All("b", Labels, Equal(
                SumOver("x", Strings, Multiply(
                    Call("star", Apply(MulVec(Tensor(Apply(V("U"), V("a"))), Psi), V("x"))),
                    Apply(MulVec(Tensor(Apply(V("U"), V("b"))), Psi), V("x")))),
                Call("ite", Equal(V("a"), V("b")), Typed(D(1), Complex), Typed(D(0), Complex)))))));

    private static Formula ReflectionDefinition() => EncodingBinders(Equal(
        LocalCall("IsCommutingReflectionEncoding", Psi, V("U")),
        Parenthesized(And(LocalCall("IsCommutingProductEncoding", Psi, V("U")),
            All("a", Labels, All("j", Sites, And(
                QualifiedCall(["Matrix", "IsHermitian"], Apply(V("U"), V("a"), V("j"))),
                Equal(Multiply(Apply(V("U"), V("a"), V("j")), Apply(V("U"), V("a"), V("j"))),
                    Typed(D(1), Qubit)))))))));

    private static Formula ClaimBody() => All("n", Nat, Imp(LE(D(1), V("n")),
        All(Psi, Arrow(Strings, Complex), Imp(
            Equal(SumOver("x", Strings, new Formula.Power(new Formula.Norm(Apply(Psi, V("x"))), D(2))),
                Typed(D(1), Real)),
            Iff(Some("U", Encoders, LocalCall("IsCommutingProductEncoding", Psi, V("U"))),
                Some("U", Encoders, LocalCall("IsCommutingReflectionEncoding", Psi, V("U"))))))));

    private static Formula EncodingBinders(Formula body) => All("n", Nat,
        All(Psi, Arrow(Strings, Complex), All("U", Encoders, body)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Sites => Call("Fin", V("n"));
    private static Formula Strings => Arrow(Sites, Call("Fin", D(2)));
    private static Formula Labels => Call("Fin", new Formula.Power(D(2), V("n")));
    private static Formula Qubit => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complex);
    private static Formula Encoders => Arrow(Labels, Arrow(Sites, Qubit));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula body, Formula type) => Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => All(V(name), type, body);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(params string[] names) => Seq(Operatorname, Grp(Seq(
        [.. names.SelectMany((name, i) => i == 0 ? new[] { V(name) } : new[] { Dot, V(name) })])));
    private static Formula QualifiedCall(string[] names, params Formula[] args) => Apply(Qualified(names), args);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Information", "CommutingEncodingReflectionClass", name);
    private static Formula LocalCall(string name, params Formula[] args) => Apply(Local(name), args);
    private static Formula Tensor(Formula factors) => QualifiedCall(
        ["D5", "S3", "Quantum", "Information", "StabilizerPairLocalUnitaryInequivalence", "tensorOp"], factors);
    private static Formula MulVec(Formula matrix, Formula vector) => QualifiedCall(["Matrix", "mulVec"], matrix, vector);
    private static Formula QubitUnitaries => QualifiedCall(["Matrix", "unitaryGroup"], Call("Fin", D(2)), Complex);
}

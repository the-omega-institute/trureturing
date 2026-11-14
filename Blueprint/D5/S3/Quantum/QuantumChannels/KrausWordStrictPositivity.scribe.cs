using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class KrausWordStrictPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/ekblad2025quantumwielandt");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full exact-length Kraus-word span forces strict positivity of the same actual iterate.",
        H("Exact Kraus words and strict positivity"),
        Blocks(
            Paragraph(Text(
                "Fix arbitrary natural numbers d and g and a family K of g complex d by d matrices. "
                + "There is no trace-preservation or unitality premise. A word of length m is indexed by "
                + "a function from Fin m to Fin g. Its coordinate zero is the leftmost, latest factor; "
                + "the product is K(w(0)) through K(w(m-1)). Reversing all tuple coordinates gives the "
                + "convention of Ekblad Section 4 without changing the set of words. The empty product "
                + "is the identity. The finite sum below ranges over every function of the indicated type.")),
            Node("word", "Exact-length Kraus products", WordFormula(),
                "The two recursion clauses specify the empty word and left multiplication by the latest letter. "
                + "The tail removes coordinate zero. This definition is earned by the actual iterate expansion.",
                DescribeRole.Definition, false),
            Node("wordSpan", "Span at exactly one length", Family(All("m", N,
                Eqn(Call("wordSpan", V("K"), V("m")),
                    Call("span", C, Call("range", Call("word", V("K"), V("m"))))))),
                "The scalar field is the complex numbers and the ambient space is the full matrix algebra. "
                + "Words of smaller lengths are not added. This is the spanning condition in equation (4.1).",
                DescribeRole.Definition, true),
            Node("iterate_eq_word_sum", "Expansion of the actual iterate", Family(All("m", N,
                All("X", Mat, Eqn(Iterate,
                    Call("sum", Lambda("w", Words,
                        Mul(Mul(Word, V("X")), Call("adjoint", Word)))))))),
                "The function being iterated is precisely MatrixMap.of_kraus K K from FiniteKrausChannel, "
                + "so its one-step action is the sum of K(i) X K(i)*. Induction splits an (m+1)-tuple "
                + "into its first letter and tail and distributes matrix multiplication over the finite sums. "
                + "The zero-length function type has one element even when g is zero.",
                DescribeRole.Theorem, false),
            Node("iterate_posDef_of_wordSpan_eq_top", "Full span implies strict positivity at the same length",
                Family(All("m", N, All("X", Mat,
                    Imp(Eqn(Call("wordSpan", V("K"), V("m")), Qualified("top")),
                        Imp(Call("PosSemidef", V("X")),
                            Imp(new Formula.Not(Eqn(V("X"), Num(0))), Call("PosDef", Iterate))))))),
                "For every nonzero positive semidefinite X the same m-th iterate is positive definite. "
                + "Each word conjugate is positive semidefinite. If the output quadratic form at a nonzero "
                + "vector v vanished, every nonnegative summand would vanish. The PSD kernel criterion "
                + "then gives X L* v = 0 for each length-m word L. The matrices A satisfying X A* v = 0 "
                + "form a complex submodule: scalar multiplication conjugates the scalar. Full word span "
                + "puts every matrix in that submodule. Choose a nonzero coordinate v(i) and test every "
                + "matrix unit E(i,b); each test forces v(i) X(a,b) = 0. Thus X = 0, a contradiction. "
                + "Zero d is covered by the impossible nonzero-input premise. Zero g and zero m are "
                + "retained with their actual word types and identity product. This is the known bridge "
                + "underlying Wielength >= primitivity index in Ekblad Section 4. It proves no quadratic "
                + "word-length bound and no quantitative bound on the gap; the global conjecture status "
                + "is unverified, and the cited source explicitly notes a proposed resolution.",
                DescribeRole.Theorem, true))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat => Call("Matrix", Fin(V("d")), Fin(V("d")), C);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Words => Arrow(Fin(V("m")), Fin(V("g")));
    private static Formula Word => Call("word", V("K"), V("m"), V("w"));
    private static Formula Iterate => Call("iterate", Call("ofkraus", V("K"), V("K")), V("m"), V("X"));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Family(Formula body) => All("d", N, All("g", N,
        All("K", Arrow(Fin(V("g")), Mat), body)));
    private static Formula WordFormula() => Family(And(
        All("w", Arrow(Fin(Num(0)), Fin(V("g"))), Eqn(Call("word", V("K"), Num(0), V("w")), Num(1))),
        All("m", N, All("w", Arrow(Fin(new Formula.Binary(V("m"), FormulaBinaryOperator.Add, Num(1))), Fin(V("g"))),
            Eqn(Call("word", V("K"), new Formula.Binary(V("m"), FormulaBinaryOperator.Add, Num(1)), V("w")),
                Mul(Call("apply", V("K"), Call("apply", V("w"), Num(0))),
                    Call("word", V("K"), V("m"), Call("tail", V("w")))))))));
}

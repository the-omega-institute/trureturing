using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class StabilizerLogicalZSupportRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/zhengliu2024magicdistillationdynamics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-qubit stabilizer code has a Z-free word in every nontrivial logical coset.",
        H("A stabilizer code without universal logical Z support"), Blocks(
            Paragraph(Text(
                "Pauli consists of the four letters I, X, Y and Z. A word on n qubits is a function "
                    + "from Fin(n), the indices 0 through n − 1, to Pauli. Scalar phases are omitted, "
                    + "as they change neither commutation nor the presence of a literal Z factor. "
                    + "This is the word description of stabilizer elements in Eq. (13). "
                    + "Pauli.rec(a,b,c,d,p) selects a, b, c or d when p is I, X, Y or Z, respectively.")),
            Node("wmul", "Phase-free multiplication of words", WordProductFormula(), Blocks(
                Paragraph(Text(
                    "Multiply the letters separately at each qubit, omitting the scalar phase of the "
                        + "Pauli matrix product. In row and column order I, X, Y, Z, the letter-product "
                        + "table has rows (I,X,Y,Z), (X,I,Z,Y), (Y,Z,I,X) and (Z,Y,X,I). "
                        + "The reused letter product is given explicitly by "), Math(LetterProductFormula()), Text(".")))),
            Node("Commutes", "Commutation from anticommuting positions", CommutesFormula(), Blocks(
                Paragraph(Text(
                    "Two words commute exactly when the number of positions with anticommuting letters "
                        + "is even. Bool.toNat sends false to zero and true to one. The letter predicate is "),
                    Math(AnticommutesFormula()), Text(
                        ". Here decide turns the displayed decidable proposition into a Boolean. "
                            + "Thus a position contributes one precisely when its letters are different "
                            + "and both belong to X, Y, Z; all other positions contribute zero.")))),
            Node("InStabilizer", "Products over subsets of the generators", StabilizerFormula(), Blocks(
                Paragraph(Text(
                    "A stabilizer word is a product of a selected subset of the r generator words. "
                        + "The selector b takes Boolean values, with true selecting its generator. "
                        + "Function.const(A, c) returns c at every argument in A. "
                        + "List.finRange(r) lists 0 through r − 1 in order. List.foldr processes this "
                        + "list from the right, starting with the all-I word and multiplying a generator "
                        + "exactly when its selector is true. The empty selection gives the all-I word. "
                        + "This describes the stabilizer elements summed in Eq. (3), modulo phase.")))),
            Node("IsStabilizerCode", "Commuting independent generators", CodeFormula(), Blocks(
                Paragraph(Text(
                    "Every pair of generator words must commute. Independence requires that a subset "
                        + "product equal to the all-I word has every selector false. Finally r < n "
                        + "requires fewer generators than qubits, leaving at least one encoded qubit. "
                        + "No further restriction on n or r is imposed.")))),
            Node("claim", "The proposed universal logical Z support", ClaimFormula(), Blocks(
                Paragraph(Text(
                    "Every stabilizer code is asserted to have a nontrivial logical word L such that "
                        + "every stabilizer translate s L contains a literal Z factor. Nontrivial means "
                        + "that L commutes with every generator and is not itself a stabilizer word. "
                        + "The conjecture following Proposition 3 and Eq. (23) implies this assertion: "
                        + "any chosen logical Z operator would provide such an L. When more than one "
                        + "qubit is encoded, the assertion asks only for one such word. "
                        + "A Y factor does not count as Z: Eq. (14) associates it with y rather than z.")))),
            Describe.Lean(
                DescribeId.Create("stabilizer-logical-z-support-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every nontrivial logical coset has a Z-free translate"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(N("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take five qubits and the four generator words XZZXI, IXZZZ, XIXZY and ZXIXY, "
                            + "in that order. They commute pairwise and are independent, and four is less "
                            + "than five. Write S for the set of all their subset products. "
                            + "The words commuting with all four form four cosets of S, with representatives "
                            + "IIIII, XXXXZ, YYYYX and ZZZZY. The first coset is S itself, so a nontrivial "
                            + "logical word belongs to one of the other three.")),
                    Paragraph(Text(
                        "The three nontrivial representatives have Z-free translates: XXXXZ times IXZZZ "
                            + "is XIYYI, YYYYX times IIIII is YYYYX, and ZZZZY times XZZXI is YIIYY. "
                            + "For any word in one of these cosets, multiply by the same stabilizer word "
                            + "that relates it to its representative, together with the displayed translating "
                            + "word. Every Pauli letter squares to I modulo phase, so the two copies of "
                            + "that stabilizer word cancel. The resulting translate is the corresponding "
                            + "Z-free word. Consequently no nontrivial logical word has a Z factor in "
                            + "every stabilizer translate. This refutes the universal support assertion; "
                            + "Proposition 3 remains a sufficient condition when its support hypothesis holds."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zheng-liu-2024-logical-z-support-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        BlockSequence commentary) => Describe.Lean(
            DescribeId.Create("stabilizer-logical-z-support-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            commentary, DescribeRole.Definition);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Q(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(N(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(N(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Q("if"), Sp, Parenthesized(condition), Sp, Q("then"), Sp, Parenthesized(yes),
            Sp, Q("else"), Sp, Parenthesized(no));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula Pauli() => Q("Pauli");
    private static Formula Letter(string name) => Q("Pauli." + name);
    private static Formula Words() => Arrow(Fin(N("n")), Pauli());
    private static Formula Selectors() => Arrow(Fin(N("r")), Q("Bool"));
    private static Formula WordBinders(Formula body) => All("n", Q("Nat"),
        All("u", Words(), All("v", Words(), body)));
    private static Formula GeneratorBinders(Formula body) => All("n", Q("Nat"), All("r", Q("Nat"),
        All("g", Arrow(Fin(N("r")), Words()), body)));
    private static Formula IdentityWord() => Call("Function.const", Fin(N("n")), Letter("I"));

    private static Formula LetterProductFormula()
    {
        var p = N("p");
        var q = N("q");
        var i = Letter("I");
        var x = Letter("X");
        var y = Letter("Y");
        var z = Letter("Z");
        return All("p", Pauli(), All("q", Pauli(), Eq(Call("letterProduct", p, q),
            Call("Pauli.rec", q, Call("Pauli.rec", x, i, z, y, q),
                Call("Pauli.rec", y, z, i, x, q), Call("Pauli.rec", z, y, x, i, q), p))));
    }

    private static Formula WordProductFormula() => WordBinders(Eq(Call("wmul", N("u"), N("v")),
        LambdaOf("i", Fin(N("n")), Call("letterProduct", At(N("u"), N("i")), At(N("v"), N("i"))))));

    private static Formula AnticommutesFormula() => All("p", Pauli(), All("q", Pauli(),
        Eq(Call("anticomm", N("p"), N("q")), Conditional(
            Or(Eq(N("p"), Letter("I")), Eq(N("q"), Letter("I"))), Q("false"),
            Call("decide", Ne(N("p"), N("q")))))));

    private static Formula CommutesFormula()
    {
        var count = Seq(new Formula.Subscript(Sum, Typed(N("i"), Fin(N("n")))), Sp,
            Parenthesized(Call("Bool.toNat", Call("anticomm", At(N("u"), N("i")), At(N("v"), N("i"))))));
        return WordBinders(IffOf(Call("Commutes", N("u"), N("v")), Eq(new Formula.Modulo(count, D(2)), D(0))));
    }

    private static Formula SubsetProduct() => Call("List.foldr",
        LambdaOf("j", Fin(N("r")), LambdaOf("w", Words(), Conditional(At(N("b"), N("j")),
            Call("wmul", At(N("g"), N("j")), N("w")), N("w")))),
        IdentityWord(), Call("List.finRange", N("r")));

    private static Formula StabilizerFormula() => GeneratorBinders(All("w", Words(),
        IffOf(Call("InStabilizer", N("g"), N("w")),
            Some("b", Selectors(), Eq(SubsetProduct(), N("w"))))));

    private static Formula CodeFormula() => GeneratorBinders(IffOf(Call("IsStabilizerCode", N("g")),
        And(All("a", Fin(N("r")), All("b", Fin(N("r")),
                Call("Commutes", At(N("g"), N("a")), At(N("g"), N("b"))))),
            And(All("b", Selectors(), Imp(Eq(SubsetProduct(), IdentityWord()),
                    All("j", Fin(N("r")), Eq(At(N("b"), N("j")), Q("false"))))),
                new Formula.Relation(N("r"), FormulaRelationOperator.LessThan, N("n"))))));

    private static Formula ClaimFormula() => IffOf(N("claim"), GeneratorBinders(
        Imp(Call("IsStabilizerCode", N("g")), Some("L", Words(),
            And(All("a", Fin(N("r")), Call("Commutes", N("L"), At(N("g"), N("a")))),
                And(new Formula.Not(Parenthesized(Call("InStabilizer", N("g"), N("L")))),
                    All("s", Words(), Imp(Call("InStabilizer", N("g"), N("s")),
                        Some("i", Fin(N("n")), Eq(At(Call("wmul", N("s"), N("L")), N("i")), Letter("Z")))))))))));
}

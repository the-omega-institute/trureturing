using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Spectral;

internal sealed class FillmanLimGapRichWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Spectral/FillmanLimGapRichWords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/fillmanlim2026gaprich");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Periodic word metrics and positive products admit compatible realizations.",
        H("FillmanLimGapRichWords"),
        Blocks(
            Entry("fl-fillmanlimgaprichwords-0", "Word", "Word",
                All("Y", V("Type"), Equal(Call("Word", V("Y")), Seq(OpenBrace, V("length"), Colon, Sp, V("PNat"), Semi, Sp, V("letter"), Colon, Sp, Arrow(Call("Fin", Cast(V("length"), Nat())), V("Y")), CloseBrace))), AssessedProvenance.FromLiterature(Source),
                "Page 5, Definition 2.2: “Given a metric space (Y,d) and k ∈ ℕ, we denote a typical element in the product space Yᵏ by y = y₁⋯yₖ. We refer to y as a word.” “The set of words over Y is denoted by” Y⋆ := ⋃ₖ₌₁∞ Yᵏ. The record stores its positive length and its zero-based finite coordinate function.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-1", "concat", "concat",
                All("Y", V("Type"), All("x", Word(V("Y")), All("y", Word(V("Y")), Equal(Call("concat", V("x"), V("y")), Pair(PlusF(App(Q("Word", "length"), V("x")), App(Q("Word", "length"), V("y"))), App(Q("Fin", "append"), Letter(V("x")), Letter(V("y")))))))), AssessedProvenance.FromLiterature(Source),
                "Page 5, Definition 2.2: “The concatenation of words y ∈ Yᵏ and z ∈ Yˡ is denoted by” y♯z = y₁⋯yₖz₁⋯zₗ ∈ Yᵏ⁺ˡ. Fin.append preserves this coordinate order.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-2", "periodicLetter", "periodicLetter",
                All("Y", V("Type"), All("x", Word(V("Y")), All("j", Nat(), Equal(Call("periodicLetter", V("x"), V("j")), App(Letter(V("x")), Pair(new Formula.Modulo(V("j"), Length(V("x"))))))))), AssessedProvenance.FromLiterature(Source),
                "Page 5, Definition 2.2: “We denote by y♯ᵐ the result of concatenating m copies of y.” The zero-based periodic index is j modulo the positive length; the angle brackets form a Fin index.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-3", "wordDistance", "wordDistance",
                All("Y", V("Type"), Instance(Call("MetricSpace", V("Y")), All("x", Word(V("Y")), All("y", Word(V("Y")), Equal(Call("wordDistance", V("x"), V("y")), App(Seq(Operatorname, Grp(V("Finset")), Dot, Operatorname, Grp(V("sup")), Apos), App(Q("Finset", "range"), Product(Length(V("x")), Length(V("y")))), Lambda("j", Nat(), Call("dist", Call("periodicLetter", V("x"), V("j")), Call("periodicLetter", V("y"), V("j")))))))))), AssessedProvenance.FromLiterature(Source),
                "Page 5, Definition 2.2: “For y ∈ Yᵏ, z ∈ Yˡ, we define” d(y,z) := sup over 1 ≤ j ≤ kl of d((y♯ˡ)ⱼ,(z♯ᵏ)ⱼ). The finite supremum uses the same positions numbered from zero; its proof of nonemptiness follows from the positive lengths and is implicit. The val operations show coercions to Nat.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-4", "extend", "extend",
                All("Y", V("Type"), All("A", Arrow(V("Y"), Arrow(Real(), Mat())), All("x", Word(V("Y")), All("E", Real(), Equal(Call("extend", V("A"), V("x"), V("E")), App(Q("List", "foldl"), Lambda("M", Mat(), Lambda("y", V("Y"), Product(App(V("A"), V("y"), V("E")), V("M")))), D(1), App(Q("List", "ofFn"), Letter(V("x"))))))))), AssessedProvenance.FromLiterature(Source),
                "Page 5, Definition 2.3: “Given a function A : Y × ℝ → SL(2,ℝ), there is a unique extension A : Y⋆ × ℝ → SL(2,ℝ) such that” A(y♯z,E) = A(z,E)A(y,E). The left fold multiplies each successive letter on the left. The matrix-valued extension also permits arbitrary real matrices.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-5", "transfer", "transfer",
                All("x", Real(), All("E", Real(), Equal(Call("transfer", V("x"), V("E")), Seq(Bang, Bang, OpenBracket, V("E"), Minus, V("x"), Comma, Sp, Minus, D(1), Semi, Sp, D(1), Comma, Sp, D(0), CloseBracket)))), AssessedProvenance.FromLiterature(Source),
                "Page 7, Definition 2.9: “The transfer matrix T : ℝ × ℝ → SL(2,ℝ) for the Schrödinger operator on ℓ²(ℤ), is given by” T(x,E) = [[E−x,−1],[1,0]]. The matrix has determinant one.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-6", "blockTransfer", "blockTransfer",
                All("k", Nat(), All("x", Space(V("k")), All("E", Real(), Equal(Call("blockTransfer", V("x"), V("E")), App(Q("List", "foldl"), Lambda("M", Mat(), Lambda("a", Real(), Product(Call("transfer", V("a"), V("E")), V("M")))), D(1), App(Q("List", "ofFn"), Lambda("i", Call("Fin", V("k")), App(V("x"), V("i"))))))))), AssessedProvenance.FromLiterature(Source),
                "Page 7, Definition 2.9: “In accordance with Definition 2.3, we also denote by T the unique extension of T to ℝ⋆ × ℝ satisfying (2.2).” EuclideanSpace coordinates are read in increasing finite-index order.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-7", "WordOver", "WordOver",
                All("Y", V("Type"), All("X", Sets(V("Y")), All("x", Word(V("Y")), Equal(Call("WordOver", V("X"), V("x")), All("i", Call("Fin", Length(V("x"))), Member(App(Letter(V("x")), V("i")), V("X"))))))), AssessedProvenance.FromRepo(Source),
                "Every letter of the positive-length word belongs to the alphabet X.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-8", "GapRichWithExceptionalSet", "GapRichWithExceptionalSet",
                All("k", Nat(), All("X", Sets(Space(V("k"))), All("S", Sets(Real()), Equal(Call("GapRichWithExceptionalSet", V("X"), V("S")), And(Call("IsDiscrete", V("S")), All("E", Real(), Imp(new Formula.Not(Parenthesized(Member(V("E"), V("S")))), All("x", Word(Space(V("k"))), Imp(Call("WordOver", V("X"), V("x")), All("epsilon", Real(), Imp(Less(D(0), V("epsilon")), Some("y", Word(Space(V("k"))), And(Call("WordOver", V("X"), V("y")), And(Less(Call("wordDistance", V("x"), V("y")), V("epsilon")), Less(D(2), Abs(Trace(Call("extend", V("blockTransfer"), V("y"), V("E"))))))))))))))))))), AssessedProvenance.FromLiterature(Source),
                "Page 6, Definition 2.7: “We say that A is gap-rich with exceptional set S ⊆ ℝ if S is discrete, and, for all E ∈ ℝ∖S, x ∈ Y⋆, and ε > 0, there exist y = y(E,x,ε) ∈ Y⋆ such that” (i) d(x,y) < ε, and (ii) A(y,E) is hyperbolic. The fixed map is the polynomial block transfer; it is continuous and has determinant one. All positive perturbing word lengths are permitted.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-9", "GapRich", "GapRich",
                All("k", Nat(), All("X", Sets(Space(V("k"))), Equal(Call("GapRich", V("X")), Some("S", Sets(Real()), Call("GapRichWithExceptionalSet", V("X"), V("S")))))), AssessedProvenance.FromLiterature(Source),
                "Page 6, Definition 2.7: “When the exact form of S is unimportant, we shall omit any mention of S and simply say that A is gap-rich. We say that X ⊆ Y is gap-rich for A if the restriction A|X×ℝ is gap-rich.” Page 7, Definition 2.9: “As above, we then simply say that a set X ⊆ ℝᵏ is gap-rich if T|X×ℝ is gap-rich in the sense of Definition 2.7.”", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-10", "cartesianProduct", "cartesianProduct",
                All("k", Nat(), All("ell", Nat(), All("Xone", Sets(Space(V("k"))), All("Xthree", Sets(Space(V("ell"))), Equal(Call("cartesianProduct", V("Xone"), V("Xthree")), Seq(OpenBrace, V("z"), Bar, Sp, Some("x", Space(V("k")), And(Member(V("x"), V("Xone")), Some("y", Space(V("ell")), And(Member(V("y"), V("Xthree")), Equal(V("z"), App(Q("WithLp", "toLp"), D(2), App(Q("Fin", "append"), App(Q("WithLp", "ofLp"), V("x")), App(Q("WithLp", "ofLp"), V("y"))))))))), CloseBrace)))))), AssessedProvenance.FromLiterature(Source),
                "Page 20, Question 2 uses “X₁ × X₃”. The product is represented in EuclideanSpace Real (Fin (k+ell)) by ordered concatenation of the first and second coordinate blocks.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-11", "wordDistanceLtIff", "wordDistanceLtIff",
                All("Y", V("Type"), Instance(Call("MetricSpace", V("Y")), All("x", Word(V("Y")), All("y", Word(V("Y")), All("epsilon", Real(), Equivalence(Less(Call("wordDistance", V("x"), V("y")), V("epsilon")), All("j", Nat(), Less(Call("dist", Call("periodicLetter", V("x"), V("j")), Call("periodicLetter", V("y"), V("j"))), V("epsilon"))))))))), AssessedProvenance.FromRepo(Source),
                "The finite product-period supremum is below epsilon exactly when every index of the two infinite periodic repetitions has distance below epsilon.", DescribeRole.Theorem),
            Entry("fl-fillmanlimgaprichwords-12", "Good", "Good",
                All("Y", V("Type"), Instance(Call("MetricSpace", V("Y")), All("x", Word(V("Y")), All("epsilon", Real(), All("y", Word(V("Y")), Equal(Call("Good", V("x"), V("epsilon"), V("y")), And(new Formula.Relation(Length(V("x")), FormulaRelationOperator.Divides, Length(V("y"))), All("i", Call("Fin", Length(V("y"))), Less(Call("dist", Call("periodicLetter", V("x"), Cast(V("i"), Nat())), App(Letter(V("y")), V("i"))), V("epsilon")))))))))), AssessedProvenance.FromRepo(Source),
                "The output length is a multiple of the input length, and each output letter is within epsilon of its corresponding periodic input letter.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-13", "goodSelf", "goodSelf",
                All("Y", V("Type"), Instance(Call("MetricSpace", V("Y")), All("x", Word(V("Y")), All("epsilon", Real(), Imp(Less(D(0), V("epsilon")), Call("Good", V("x"), V("epsilon"), V("x"))))))), AssessedProvenance.FromRepo(Source),
                "Every word has the multiple-length closeness property to itself for positive epsilon.", DescribeRole.Theorem),
            Entry("fl-fillmanlimgaprichwords-14", "goodDistance", "goodDistance",
                All("Y", V("Type"), Instance(Call("MetricSpace", V("Y")), All("x", Word(V("Y")), All("y", Word(V("Y")), All("epsilon", Real(), Imp(Call("Good", V("x"), V("epsilon"), V("y")), Less(Call("wordDistance", V("x"), V("y")), V("epsilon")))))))), AssessedProvenance.FromRepo(Source),
                "Multiple-length coordinate closeness implies closeness in the periodic word distance.", DescribeRole.Theorem),
            Entry("fl-fillmanlimgaprichwords-15", "foldLeftStart", "foldLeftStart",
                All("Y", V("Type"), All("f", Arrow(V("Y"), Mat()), All("l", Call("List", V("Y")), All("M", Mat(), Equal(App(Q("List", "foldl"), Lambda("B", Mat(), Lambda("a", V("Y"), Product(App(V("f"), V("a")), V("B")))), V("M"), V("l")), Product(App(Q("List", "foldl"), Lambda("B", Mat(), Lambda("a", V("Y"), Product(App(V("f"), V("a")), V("B")))), D(1), V("l")), V("M"))))))), AssessedProvenance.FromRepo(Source),
                "The left fold of left-multiplication acts on any starting matrix by right multiplication of the fold starting at the identity.", DescribeRole.Theorem),
            Entry("fl-fillmanlimgaprichwords-16", "wordOfList", "wordOfList",
                All("Y", V("Type"), All("l", Call("List", V("Y")), All("hl", Less(D(0), App(Q("List", "length"), V("l"))), Equal(Call("wordOfList", V("l"), V("hl")), Pair(Pair(App(Q("List", "length"), V("l")), V("hl")), Lambda("i", Call("Fin", App(Q("List", "length"), V("l"))), App(Q("List", "get"), V("l"), V("i")))))))), AssessedProvenance.FromRepo(Source),
                "A list with positive length determines a Word whose positive length and indexed letters are the list length and List.get.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichwords-17", "wordOfListLetters", "wordOfListLetters",
                All("Y", V("Type"), All("l", Call("List", V("Y")), All("hl", Less(D(0), App(Q("List", "length"), V("l"))), Equal(App(Q("List", "ofFn"), Letter(Call("wordOfList", V("l"), V("hl")))), V("l"))))), AssessedProvenance.FromRepo(Source),
                "Enumerating the letters of wordOfList recovers the original list.", DescribeRole.Theorem),
            Entry("fl-fillmanlimgaprichwords-18", "goodOfForallTwo", "goodOfForallTwo",
                All("Y", V("Type"), Instance(Call("MetricSpace", V("Y")), All("x", Word(V("Y")), All("y", Word(V("Y")), All("epsilon", Real(), Imp(App(Seq(Operatorname, Grp(V("List")), Dot, Operatorname, Grp(V("Forall")), Underscore, Grp(D(2))), Lambda("a", V("Y"), Lambda("b", V("Y"), Less(Call("dist", V("a"), V("b")), V("epsilon")))), App(Q("List", "ofFn"), Letter(V("x"))), App(Q("List", "ofFn"), Letter(V("y")))), Call("Good", V("x"), V("epsilon"), V("y")))))))), AssessedProvenance.FromRepo(Source),
                "Pointwise List.Forall₂ closeness of the two complete coordinate lists gives equal lengths and the multiple-length closeness property.", DescribeRole.Theorem),
            Entry("fl-fillmanlimgaprichwords-19", "closureWordRealization", "closureWordRealization",
                All("Y", V("Type"), Instance(Call("MetricSpace", V("Y")), All("X", Sets(V("Y")), All("A", Arrow(V("Y"), Arrow(Real(), Mat())), All("x", Word(V("Y")), All("y", Word(V("Y")), All("E", Real(), All("epsilon", Real(), All("C", Mat(), Imp(Call("Good", V("x"), V("epsilon"), V("x")), Imp(Call("Good", V("x"), V("epsilon"), V("y")), Imp(Call("WordOver", V("X"), V("x")), Imp(Call("WordOver", V("X"), V("y")), Imp(Member(V("C"), App(Q("Submonoid", "closure"), new Formula.SetLiteral([Call("extend", V("A"), V("x"), V("E")), Call("extend", V("A"), V("y"), V("E"))]))), Or(Equal(V("C"), D(1)), Some("z", Word(V("Y")), And(Call("WordOver", V("X"), V("z")), And(Call("Good", V("x"), V("epsilon"), V("z")), Equal(Call("extend", V("A"), V("z"), V("E")), V("C")))))))))))))))))))), AssessedProvenance.FromRepo(Source),
                "Every matrix in the submonoid generated by the two word transfers is the identity or the transfer of a word over X satisfying the same multiple-length closeness property to x. Concatenation realizes multiplication in the reversed order.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);


    private static Formula V(string name) => F.Id(name);
    private static Formula Q(params string[] parts) => Seq([.. parts.SelectMany((s, i) => i == 0 ? new[] { Operatorname, Grp(F.Id(s)) } : new[] { Dot, Operatorname, Grp(F.Id(s)) })]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(V(name), args);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Lambda(string n, Formula t, Formula b) => Parenthesized(Seq(V("fun"), Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, b));
    private static Formula Cast(Formula x, Formula t) => Call("val", x, t);
    private static Formula Nat() => V("Nat");
    private static Formula Real() => V("Real");
    private static Formula Mat() => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Real());
    private static Formula Space(Formula k) => Call("EuclideanSpace", Real(), Call("Fin", k));
    private static Formula Sets(Formula x) => Call("Set", x);
    private static Formula Word(Formula x) => Call("Word", x);
    private static Formula Length(Formula x) => Cast(App(Q("Word", "length"), x), Nat());
    private static Formula Letter(Formula x) => App(Q("Word", "letter"), x);
    private static Formula Trace(Formula x) => App(Q("Matrix", "trace"), x);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Star, Sp, Parenthesized(b));
    private static Formula PlusF(Formula a, Formula b) => Seq(Parenthesized(a), Plus, Parenthesized(b));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula Pair(params Formula[] xs) => Seq(Langle, Sp, Seq([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x })]), Sp, Rangle);
    private static Formula Instance(Formula t, Formula body) => Seq(OpenBracket, t, CloseBracket, Sp, body);
}

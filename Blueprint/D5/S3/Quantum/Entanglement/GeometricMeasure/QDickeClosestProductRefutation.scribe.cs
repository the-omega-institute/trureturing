using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GeometricMeasure;

internal sealed class QDickeClosestProductRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/LieTheory/ballesterosetal2025qsymmetric");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At q equal to four, no closest normalized product vector to the one-excitation three-qubit q-Dicke state is q-symmetric.",
        H("Closest product vectors need not be q-symmetric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dicke-one"), DeclarationHandle.Create(Module + ".dicke1"),
                H("The one-excitation q-Dicke vector"),
                StatementSource.FromAuthor(Disp(DickeFormula(false))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "With zero denoting down and one denoting up, the nonzero coordinates are at "
                    + "(0,0,1), (0,1,0) and (1,0,0), with respective coefficients sqrt(q), one and "
                    + "the inverse of sqrt(q), divided by sqrt(q + 1 + q inverse). For positive q this "
                    + "is the normalized one-excitation state in the v3 TeX, line 581; the q-number "
                    + "at line 469 gives [3]_q = q + 1 + q inverse. The formula defines a vector "
                    + "for every real q, without asserting normalization outside the positive range. "
                    + "Complex.ofReal explicitly includes each real square root in the complex scalars."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dicke-two"), DeclarationHandle.Create(Module + ".dicke2"),
                H("The two-excitation q-Dicke vector"),
                StatementSource.FromAuthor(Disp(DickeFormula(true))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The two-excitation vector has the same three coefficients and denominator, "
                    + "now at (0,1,1), (1,0,1) and (1,1,0). For positive q this is the normalized "
                    + "state in the v3 TeX, line 582. Its displayed expression is defined for every real q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q-symmetric-subspace"), DeclarationHandle.Create(Module + ".symQ"),
                H("The three-qubit q-symmetric span"),
                StatementSource.FromAuthor(Disp(SpanFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Take the complex linear span of the all-zero coordinate vector, the "
                    + "one-excitation and two-excitation vectors, and the all-one coordinate vector. "
                    + "For positive q this is the three-qubit q-symmetric subspace described in "
                    + "the v3 TeX, lines 579–586. The definition itself allows every real q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("product-vector"), DeclarationHandle.Create(Module + ".prod"),
                H("An ordinary three-qubit product vector"),
                StatementSource.FromAuthor(Disp(ProductFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Multiply the three local complex coordinates to form the ordinary tensor "
                    + "product, as in the v3 TeX, lines 1238–1242. The index is the right-associated "
                    + "pair (p.1,(p.2.1,p.2.2)); WithLp.ofLp gives the coordinate function of each "
                    + "Euclidean vector. No unit-norm condition is part of this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("closest-product"), DeclarationHandle.Create(Module + ".IsClosestProduct"),
                H("Maximal overlap among normalized product vectors"),
                StatementSource.FromAuthor(Disp(ClosestFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The three local vectors have norm one, and their product has overlap modulus "
                    + "with dicke1 q at least as large as that of every other normalized product. "
                    + "This specializes the geometric optimization in the v3 TeX, lines 1234–1243, "
                    + "to the one-excitation three-qubit state. The inner product and all local "
                    + "norms are the ordinary complex Euclidean ones."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Module + ".claim"),
                H("A q-symmetric closest product for every positive deformation"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every positive real q, some normalized product maximizing the ordinary "
                    + "overlap with dicke1 q belongs to the q-symmetric span. This is the "
                    + "one-excitation, three-qubit instance of the conjecture for arbitrary "
                    + "q-Dicke states in the v3 TeX, line 1258."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("The obstruction at q equal to four"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a unit complex qubit, the squared moduli of its two coordinates sum "
                        + "to one. The squared scalar Cauchy–Schwarz inequality bounds the squared modulus "
                        + "of xu + yv by the product of the squared coordinate norms of (x,y) "
                        + "and (u,v). These two facts control all the product overlaps below.")),
                    Paragraph(Text(
                        "At q = 4 the one-excitation vector is (4|001> + 2|010> + |100>)/sqrt(21). "
                        + "Its inner product with prod a b c is "
                        + "(4 a(0)b(0)c(1) + (2 a(0)b(1) + a(1)b(0))c(0))/sqrt(21). "
                        + "Squaring its modulus and multiplying by 21 therefore gives the squared "
                        + "modulus of this numerator.")),
                    Paragraph(Text(
                        "For unit a,b,c, apply Cauchy–Schwarz first to the numerator with the "
                        + "coordinates c(1),c(0), and then to 2 a(0)b(1) + a(1)b(0) with "
                        + "coefficients 2,1. Put A = |a(0)| squared and B = |b(0)| squared. "
                        + "Normalization gives 21 times the squared overlap at most "
                        + "16AB + 5(A(1-B) + (1-A)B) = 5A + 5B + 6AB.")),
                    Paragraph(Text(
                        "The normalized product |0> tensor |0> tensor |1> has squared overlap "
                        + "16/21. Any maximizing triple a,b,c consequently has squared overlap "
                        + "at least 16/21. Since A and B each lie between zero and one, AB is at "
                        + "most one; the preceding bound then forces A = B = 1. Thus a(1) = b(1) = 0. "
                        + "The squared-overlap identity and normalization of c force |c(1)| squared "
                        + "to equal one and c(0) = 0. In particular a(0)b(0)c(1) is nonzero.")),
                    Paragraph(Text(
                        "Every vector v in symQ 4 satisfies v(0,0,1) = 2 v(0,1,0). Indeed, the "
                        + "complex linear functional taking v to v(0,0,1) - 2 v(0,1,0) vanishes "
                        + "on each of the four spanning vectors. The all-zero, all-one and "
                        + "two-excitation vectors have both coordinates zero; dicke1 4 has "
                        + "coordinates 4/sqrt(21) and 2/sqrt(21). Their span therefore lies in its kernel. "
                        + "For a maximizing product, membership in this span would give "
                        + "a(0)b(0)c(1) = 2 a(0)b(1)c(0) = 0, contradicting the nonzero product "
                        + "just obtained. Finally, the asserted universal existence at positive q "
                        + "would supply such a maximizing product in the span at q = 4, a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ballesteros-et-al-2025-qdicke-closest-product"),
                    ResolutionKind.Refuted)))));

    private static Formula DickeFormula(bool two)
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var root = OfReal(At(Qualified("Real", "sqrt"), q));
        var first = two ? Triple(0, 1, 1) : Triple(0, 0, 1);
        var second = two ? Triple(1, 0, 1) : Triple(0, 1, 0);
        var third = two ? Triple(1, 1, 0) : Triple(1, 0, 0);
        var numerator = If(Equal(p, first), root,
            If(Equal(p, second), Typed(D(1), Complexes),
                If(Equal(p, third), Inverse(root), Typed(D(0), Complexes))));
        var denominator = OfReal(At(Qualified("Real", "sqrt"),
            Add(Add(q, Typed(D(1), Reals)), Inverse(q))));
        var value = At(Qualified("WithLp", "toLp"), D(2),
            LambdaOf("p", TripleType, new Formula.Fraction(numerator, denominator)));
        return All("q", Reals, Equal(Typed(LocalCall(two ? "dicke2" : "dicke1", q), ThreeQubits), value));
    }

    private static Formula SpanFormula() => All("q", Reals,
        Equal(Typed(LocalCall("symQ", F.Id("q")), At(Qualified("Submodule"), Complexes, ThreeQubits)),
            At(Qualified("Submodule", "span"), Complexes,
                Seq(OpenBrace, At(Qualified("EuclideanSpace", "single"), Triple(0, 0, 0), Typed(D(1), Complexes)),
                    Comma, Sp, LocalCall("dicke1", F.Id("q")), Comma, Sp, LocalCall("dicke2", F.Id("q")),
                    Comma, Sp, At(Qualified("EuclideanSpace", "single"), Triple(1, 1, 1), Typed(D(1), Complexes)),
                    CloseBrace))));

    private static Formula ProductFormula()
    {
        var p = F.Id("p");
        var value = Multiply(Multiply(Coordinate(F.Id("a"), First(p)),
            Coordinate(F.Id("b"), First(Second(p)))), Coordinate(F.Id("c"), Second(Second(p))));
        return ProductBinders(Equal(Typed(LocalCall("prod", F.Id("a"), F.Id("b"), F.Id("c")), ThreeQubits),
            At(Qualified("WithLp", "toLp"), D(2), LambdaOf("p", TripleType, value))));
    }

    private static Formula ClosestFormula()
    {
        var other = All("a'", Qubit, All("b'", Qubit, All("c'", Qubit,
            Implies(Unit(Variable("a'")), Implies(Unit(Variable("b'")), Implies(Unit(Variable("c'")),
                new Formula.Relation(Overlap(Variable("a'"), Variable("b'"), Variable("c'")),
                    FormulaRelationOperator.LessThanOrEqual, Overlap(F.Id("a"), F.Id("b"), F.Id("c")))))))));
        return All("q", Reals, ProductBinders(Equal(
            Typed(LocalCall("IsClosestProduct", F.Id("q"), F.Id("a"), F.Id("b"), F.Id("c")), Qualified("Prop")),
            Parenthesized(And(Unit(F.Id("a")), And(Unit(F.Id("b")), And(Unit(F.Id("c")), other)))))));
    }

    private static Formula ClaimBody() => All("q", Reals,
        Implies(new Formula.Relation(Typed(D(0), Reals), FormulaRelationOperator.LessThan, F.Id("q")),
            Some("a", Qubit, Some("b", Qubit, Some("c", Qubit,
                And(LocalCall("IsClosestProduct", F.Id("q"), F.Id("a"), F.Id("b"), F.Id("c")),
                    new Formula.Relation(LocalCall("prod", F.Id("a"), F.Id("b"), F.Id("c")),
                        FormulaRelationOperator.MemberOf, LocalCall("symQ", F.Id("q")))))))));

    private static Formula ProductBinders(Formula body) =>
        All("a", Qubit, All("b", Qubit, All("c", Qubit, body)));
    private static Formula Overlap(Formula a, Formula b, Formula c) => new Formula.Norm(
        At(Qualified("inner"), Complexes, LocalCall("dicke1", F.Id("q")), LocalCall("prod", a, b, c)));
    private static Formula Unit(Formula value) => Equal(new Formula.Norm(value), Typed(D(1), Reals));
    private static Formula Coordinate(Formula value, Formula index) =>
        At(Qualified("WithLp", "ofLp"), value, index);
    private static Formula First(Formula value) => Seq(Parenthesized(value), Dot, D(1));
    private static Formula Second(Formula value) => Seq(Parenthesized(value), Dot, D(2));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Triple(byte a, byte b, byte c) =>
        Pair(Typed(D(a), FinTwo), Pair(Typed(D(b), FinTwo), Typed(D(c), FinTwo)));
    private static Formula TripleType => Parenthesized(Seq(FinTwo, Sp, Times, Sp,
        Parenthesized(Seq(FinTwo, Sp, Times, Sp, FinTwo))));
    private static Formula FinTwo => At(Qualified("Fin"), D(2));
    private static Formula Qubit => At(Qualified("EuclideanSpace"), Complexes, FinTwo);
    private static Formula ThreeQubits => At(Qualified("EuclideanSpace"), Complexes, TripleType);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula OfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Inverse(Formula value) => At(Qualified("Inv", "inv"), value);
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(Variable(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(Variable(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(Variable(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Variable(string name) => name switch
    {
        "a'" => Seq(F.Id("a"), Apos),
        "b'" => Seq(F.Id("b"), Apos),
        "c'" => Seq(F.Id("c"), Apos),
        _ => F.Id(name),
    };
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Entanglement", "GeometricMeasure",
        "QDickeClosestProductRefutation", name);
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
}

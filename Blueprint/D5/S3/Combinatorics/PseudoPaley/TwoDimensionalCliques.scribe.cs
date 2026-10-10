using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PseudoPaley;

internal sealed class TwoDimensionalCliquesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/asgarli2021pseudopaley");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-dimensional cliques containing one in quartic pseudo-Paley graphs are exactly the odd-generator planes.",
        H("Two-dimensional pseudo-Paley cliques"),
        Blocks(
            Node("chi", "Cyclotomic class character", DescribeRole.Definition, ChiFormula(),
                "The power character labels the p+1 cyclotomic classes of the quartic finite field."),
            Node("Q", "Norm of an affine representative", DescribeRole.Definition, QFormula(),
                "Q is the p-squared norm power of b+t; it is used on prime-field affine parameters."),
            Node("chi_eq_Q_pow", "Character through the norm", DescribeRole.Lemma, ChiNormFormula(),
                "The character factors as the norm power followed by the p-minus-one power."),
            Node("pow_char_eq_self_of_pow_sub_one_eq_one", "A fixed prime-field element", DescribeRole.Lemma, FixedPowerFormula(),
                "A p-minus-one root of unity is fixed by the p-th power."),
            Node("q_factor", "Quartic exponent factorization", DescribeRole.Lemma, FactorFormula(),
                "All arithmetic is in the natural numbers; subtraction is truncated subtraction."),
            Node("c_square_iff_even", "Parity of the norm", DescribeRole.Lemma, ParityFormula(),
                "The norm of the indicated generator power lies in the prime field and is a square exactly when its exponent index is even."),
            Node("trace_norm_fixed_implies_fixed", "Trace and norm prevent collapse", DescribeRole.Lemma, TraceFormula(),
                "If both the relative trace and norm are fixed by the p-th power, their common source element is fixed as well."),
            Node("normPoly", "The affine norm polynomial", DescribeRole.Definition, NormPolyFormula(),
                "The polynomial expression retains its leading coefficient one."),
            Node("cross_eq_iff", "Two affine points share a class", DescribeRole.Lemma, CrossFormula(),
                "When the trace coefficient is outside the prime field and the norm is inside it, proportional norms occur exactly for equal points or for a pair whose product is the norm."),
            Node("infinity_cross_iff", "The affine mate of infinity", DescribeRole.Lemma, InfinityFormula(),
                "The prime-field norm direction has exactly the affine parameter zero."),
            Node("projectiveMate", "The projective pairing", DescribeRole.Definition, MateFormula(),
                "Option.none represents infinity. It exchanges infinity with zero and sends each nonzero parameter to C/t, avoiding total division at zero."),
            Node("projectiveMate_no_fixed_iff", "Nonsquares have no singleton orbits", DescribeRole.Lemma, NoFixedFormula(),
                "For a nonzero norm the projective pairing is fixed-point-free precisely when the norm is not a square."),
            Node("projectiveClass", "Projective class map", DescribeRole.Definition, ProjectiveFormula(),
                "Infinity represents one and an affine prime-field parameter represents b+t."),
            Node("norm_Q_ne_zero", "Nonzero affine norms", DescribeRole.Lemma, NormNonzeroFormula(),
                "An element outside the prime field cannot be cancelled by a prime-field affine parameter."),
            Node("Q_as_quadratic", "Quadratic expansion of the norm", DescribeRole.Lemma, ExpansionFormula(),
                "The norm has quadratic, trace and constant terms, with every affine parameter mapped into the quartic field."),
            Node("equal_projective_class_cross", "Equality gives proportional norm directions", DescribeRole.Lemma, ProjectiveCrossFormula(),
                "Equal class characters force the p-th-power cross product equality of the two nonzero norms."),
            Node("prime_field_fixed", "Embedded prime-field parameters", DescribeRole.Lemma, PrimeFixedFormula(),
                "Every embedded prime-field parameter is fixed by the p-th power."),
            Node("projective_fiber_card_le_two", "At most two projective points per class", DescribeRole.Theorem, FiberFormula(),
                "For b outside the prime field, the affine fiber equation is a nonzero polynomial of degree at most two. The infinity fiber has a nonzero linear equation on its affine part. The two bounds give at most two points in every projective fiber."),
            Describe.Lean(DescribeId.Create("cyclotomic-class"), DeclarationHandle.Create(Prefix + "cyclotomicClass"),
                H("Cyclotomic class"), StatementSource.FromAuthor(Disp(ClassFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(CyclotomicQuote(), Paragraph(Text("The source takes the p+1-th cyclotomic classes of the quartic finite field. The primitive element is g, and natural exponents enumerate the cyclic subgroup generated by its p+1-th power."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("connection"), DeclarationHandle.Create(Prefix + "connection"),
                H("Connection set"), StatementSource.FromAuthor(Disp(ConnectionFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(DefinitionQuote(), Paragraph(Text("Here the source parameters are q=p^4 and 2d=p+1; the selected natural indices form I. The union is the literal connection set."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pseudo-paley"), DeclarationHandle.Create(Prefix + "PP"),
                H("Pseudo-Paley graph"), StatementSource.FromAuthor(Disp(GraphFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(DefinitionQuote(), Paragraph(Text("SimpleGraph.fromRel supplies the symmetric irreflexive relation of the additive Cayley graph; the difference is y-x."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Asgarli–Yip Conjecture 5.9"), StatementSource.FromAuthor(Disp(Eq(Typed(X("claim"), X("Prop")), ClaimFormula()))),
                AssessedProvenance.FromLiterature(Source), Blocks(ConjectureQuote(), Paragraph(Text(
                    "The prime p is odd, g has order p^4-1, and V is a two-dimensional ZMod p-subspace containing one. The source's 'for some I' means I is contained in Finset.range (p+1) and has cardinality Nat.div (p+1) 2. The direct sum is Submodule.span of one and the indicated generator power. Natural odd indices enumerate the same powers as odd integer indices, because the order p^4-1 is even."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Classification of the two-dimensional cliques"), StatementSource.FromAuthor(Disp(X("claim"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The p+1 projective points map to cyclotomic classes with at most two points per fiber. A clique fits into (p+1)/2 classes, forcing every fiber to be a pair. The mate of infinity selects a generator power in the zeroth class. Its norm is a square exactly for even indices; a square norm gives a singleton fiber, so clique indices are odd. Conversely, an odd index gives a nonsquare norm and the fixed-point-free pairing exchanges zero with infinity and pairs the other parameters by C/t. Its classes form the required index set."))), DescribeRole.Theorem)), []));

    private static Formula ClassFormula() => PrimeBody(Alls([("g", FieldType()), ("j", Nat())], Eq(
        Call("cyclotomicClass", X("p"), X("g"), X("j")), SetOf("x", FieldType(), Ex("m", Nat(), Eq(
            X("x"), Pow(X("g"), Add(X("j"), Mul(Add(X("p"), D(1)), X("m"))))))))));
    private static Formula ConnectionFormula() => PrimeBody(Alls([("g", FieldType()), ("I", Call("Finset", Nat()))], Eq(
        Call("connection", X("p"), X("g"), X("I")), App(Qualified("Set", "iUnion"), LambdaOf("j", Nat(),
            App(Qualified("Set", "iUnion"), Seq(LambdaLower, Sp, Typed(Underscore, Mem(X("j"), X("I"))), Sp, Mapsto, Sp,
                Call("cyclotomicClass", X("p"), X("g"), X("j")))))))));
    private static Formula GraphFormula() => PrimeBody(Alls([("g", FieldType()), ("I", Call("Finset", Nat()))], Eq(
        Call("PP", X("p"), X("g"), X("I")), App(Qualified("SimpleGraph", "fromRel"),
            LambdaOf("x", FieldType(), LambdaOf("y", FieldType(), Mem(Sub(X("y"), X("x")), Call("connection", X("p"), X("g"), X("I")))))))));
    private static Formula ClaimFormula()
    {
        var p = X("p"); var g = X("g"); var V = X("V"); var I = X("I"); var k = X("k");
        var graph = Call("PP", p, g, I);
        var clique = App(Qualified("SimpleGraph", "IsClique"), graph, Typed(V, Call("Set", FieldType())));
        var selected = Ex("I", Call("Finset", Nat()), And(SubsetOf(I, App(Qualified("Finset", "range"), Add(p, D(1)))),
            And(Eq(Card(I), App(Qualified("Nat", "div"), Add(p, D(1)), D(2))), clique)));
        var plane = Ex("k", Nat(), And(Call("Odd", k), Eq(V, App(Qualified("Submodule", "span"), PrimeType(),
            new Formula.SetLiteral([D(1), Pow(g, Mul(Add(p, D(1)), k))])))));
        return PrimeBody(Imp(Ne(p, D(2)), All("g", FieldType(), Imp(Call("IsPrimitiveRoot", g, Sub(Pow(p, D(4)), D(1))),
            All("V", Call("Submodule", PrimeType(), FieldType()), Imp(And(Eq(App(Qualified("Module", "finrank"), PrimeType(), V), D(2)), Mem(Typed(D(1), FieldType()), V)),
                IffOf(selected, plane)))))));
    }
    private static DocumentBlock ConjectureQuote() => Paragraph(Text("Conjecture 5.9 (p. 17): “Let "),
        Math(X("V")), Text(" be a "), Math(D(2)), Text("-dimensional subspace in "),
        Math(SourceField(Pow(X("p"), D(4)))), Text(", such that "), Math(Mem(D(1), X("V"))),
        Text(". Then "), Math(X("V")), Text(" is a clique in "),
        Math(Call("PP", Pow(X("p"), D(4)), Add(X("p"), D(1)), X("I"))), Text(" for some "),
        Math(X("I")), Text(" if and only if "), Math(Eq(X("V"), SourceField(X("p")))),
        Text(" ⊕ "), Math(Seq(X("a"), SourceField(X("p")))), Text(", where "),
        Math(Eq(X("a"), Pow(X("g"), Seq(Parenthesized(Add(X("p"), D(1))), X("k"))))), Text(" and "),
        Math(X("k")), Text(" is an odd integer.”"));
    private static Formula SourceField(Formula q) => new Formula.Subscript(Seq(Mathbb, Grp(X("F"))), q);
    private static Formula SourceClass(Formula j) => new Formula.Subscript(X("C"), j);
    private static DocumentBlock CyclotomicQuote() => Paragraph(Text("Cyclotomic classes (p. 1): “Let "),
        Math(new Formula.Relation(X("N"), FormulaRelationOperator.Divides, Parenthesized(Sub(X("q"), D(1))))),
        Text(". Let "), Math(SourceClass(D(0))), Text(" be the subgroup of "),
        Math(Pow(SourceField(X("q")), Star)), Text(" with index "), Math(X("N")),
        Text(", and let "), Math(SourceClass(D(1))), Text(", …, "), Math(SourceClass(Sub(X("N"), D(1)))),
        Text(" be all the cosets of "), Math(SourceClass(D(0))), Text(", where "),
        Math(Eq(SourceClass(X("j")), Seq(Pow(X("g"), X("j")), SourceClass(D(0))))),
        Text(". The sets "), Math(SourceClass(D(0))), Text(", "), Math(SourceClass(D(1))),
        Text(", …, "), Math(SourceClass(Sub(X("N"), D(1)))), Text(" are called the "),
        Math(X("N")), Text("-th cyclotomic classes of "), Math(SourceField(X("q"))), Text(".”"));
    private static DocumentBlock DefinitionQuote() => Paragraph(Text("Definition 1.1 (pp. 1–2): “Suppose "),
        Math(X("q")), Text(" is a prime power, "), Math(X("d")), Text(" a positive integer such that "),
        Math(new Formula.Relation(Seq(D(2), X("d")), FormulaRelationOperator.Divides, Parenthesized(Sub(X("q"), D(1))))),
        Text(", and "), Math(X("I")), Text("={"), Math(new Formula.Subscript(X("m"), D(1))),
        Text(", …, "), Math(new Formula.Subscript(X("m"), X("d"))), Text("} ⊂ {0, 1, …, "),
        Math(Sub(Seq(D(2), X("d")), D(1))), Text("} with "), Math(Eq(Seq(Bar, X("I"), Bar), X("d"))),
        Text(". Let "), Math(SourceClass(D(0))), Text(", "), Math(SourceClass(D(1))), Text(", …, "),
        Math(SourceClass(Sub(Seq(D(2), X("d")), D(1)))), Text(" be the "), Math(Seq(D(2), X("d"))),
        Text("-th cyclotomic classes of "), Math(SourceField(X("q"))), Text(". The graph "),
        Math(Call("PP", X("q"), Seq(D(2), X("d")), X("I"))), Text(" is defined to be the Cayley graph "),
        Math(Call("Cay", Pow(SourceField(X("q")), Plus), X("D"))), Text(" where D=⋃ⱼ₌₁ᵈ "),
        Math(SourceClass(new Formula.Subscript(X("m"), X("j")))), Text(".”"));
    private static Formula X(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Alls((string Name, Formula Type)[] binders, Formula body)
    {
        for (var i = binders.Length - 1; i >= 0; i--) body = All(binders[i].Name, binders[i].Type, body);
        return body;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula SubsetOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula FieldType() => Call("GaloisField", X("p"), D(4));
    private static Formula PrimeType() => Call("ZMod", X("p"));
    private static Formula PrimeBody(Formula body) => All("p", Nat(), Instance(Call("Fact", App(Qualified("Nat", "Prime"), X("p"))), body));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Card(Formula s) => App(Qualified("Finset", "card"), s);
    private static Formula LambdaOf(string v, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(v), type), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string v, Formula type, Formula pred) => Seq(OpenBrace, Typed(X(v), type), Sp, Mid, Sp, pred, CloseBrace);

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula ChiFormula() => PrimeBody(All("x", FieldType(),
        Eq(Chi(X("x")), Pow(X("x"), Mul(Add(Pow(X("p"), D(2)), D(1)), Sub(X("p"), D(1)))))));
    private static Formula QFormula() => PrimeBody(Alls([("b", FieldType()), ("t", FieldType())],
        Eq(NormQ(X("b"), X("t")), Pow(Add(X("b"), X("t")), Add(Pow(X("p"), D(2)), D(1))))));
    private static Formula ChiNormFormula() => PrimeBody(Alls([("b", FieldType()), ("t", FieldType())],
        Eq(Chi(Add(X("b"), X("t"))), Pow(NormQ(X("b"), X("t")), Sub(X("p"), D(1))))));
    private static Formula FixedPowerFormula() => PrimeBody(All("x", FieldType(), Imp(
        Eq(Pow(X("x"), Sub(X("p"), D(1))), D(1)), Eq(Pow(X("x"), X("p")), X("x")))));
    private static Formula FactorFormula() => All("p", Nat(), Imp(LeqOf(D(1), X("p")), Eq(
        Mul(Sub(X("p"), D(1)), Mul(Add(X("p"), D(1)), Add(Pow(X("p"), D(2)), D(1)))), Sub(Pow(X("p"), D(4)), D(1)))));
    private static Formula ParityFormula() => PrimeBody(Imp(Ne(X("p"), D(2)), All("g", FieldType(), Imp(
        Call("IsPrimitiveRoot", X("g"), Sub(Pow(X("p"), D(4)), D(1))), All("k", Nat(), Ex("u", PrimeType(), And(
            Eq(Cast(X("u")), Pow(Pow(X("g"), Mul(Add(X("p"), D(1)), X("k"))), Add(Pow(X("p"), D(2)), D(1)))),
            IffOf(Call("IsSquare", X("u")), Call("Even", X("k"))))))))));
    private static Formula TraceFormula() => GenericChar(All("b", X("F"), Imp(And(
        Eq(Pow(Add(X("b"), Pow(X("b"), Pow(X("p"), D(2)))), X("p")), Add(X("b"), Pow(X("b"), Pow(X("p"), D(2))))),
        Eq(Pow(Mul(X("b"), Pow(X("b"), Pow(X("p"), D(2)))), X("p")), Mul(X("b"), Pow(X("b"), Pow(X("p"), D(2)))))),
        Eq(Pow(X("b"), X("p")), X("b")))));
    private static Formula NormPolyFormula() => GenericField(Alls([("B", X("F")), ("C", X("F")), ("t", X("F"))],
        Eq(NormPoly(X("B"), X("C"), X("t")), Add(Add(Pow(X("t"), D(2)), Mul(X("B"), X("t"))), X("C")))));
    private static Formula CrossFormula() => GenericChar(Alls([("B", X("F")), ("C", X("F")), ("t", X("F")), ("s", X("F"))],
        Imp(And(And(Ne(Pow(X("B"), X("p")), X("B")), Eq(Pow(X("C"), X("p")), X("C"))),
            And(Eq(Pow(X("t"), X("p")), X("t")), Eq(Pow(X("s"), X("p")), X("s")))),
            IffOf(Eq(Mul(Pow(NormPoly(X("B"), X("C"), X("t")), X("p")), NormPoly(X("B"), X("C"), X("s"))),
                Mul(NormPoly(X("B"), X("C"), X("t")), Pow(NormPoly(X("B"), X("C"), X("s")), X("p")))),
                Or(Eq(X("t"), X("s")), Eq(Mul(X("t"), X("s")), X("C")))))));
    private static Formula InfinityFormula() => GenericChar(Alls([("B", X("F")), ("C", X("F")), ("t", X("F"))],
        Imp(And(And(Ne(Pow(X("B"), X("p")), X("B")), Eq(Pow(X("C"), X("p")), X("C"))), Eq(Pow(X("t"), X("p")), X("t"))),
            IffOf(Eq(Pow(NormPoly(X("B"), X("C"), X("t")), X("p")), NormPoly(X("B"), X("C"), X("t"))), Eq(X("t"), D(0))))));
    private static Formula MateFormula() => GenericField(All("C", X("F"),
        And(Eq(Mate(X("C"), None()), Some(D(0))), All("t", X("F"), And(
            Imp(Eq(X("t"), D(0)), Eq(Mate(X("C"), Some(X("t"))), None())),
            Imp(Ne(X("t"), D(0)), Eq(Mate(X("C"), Some(X("t"))), Some(new Formula.Fraction(X("C"), X("t"))))))))));
    private static Formula NoFixedFormula() => GenericField(All("C", X("F"), Imp(Ne(X("C"), D(0)),
        IffOf(All("x", Call("Option", X("F")), Ne(Mate(X("C"), X("x")), X("x"))), NotOf(Call("IsSquare", X("C")))))));
    private static Formula ProjectiveFormula() => PrimeBody(All("b", FieldType(), And(
        Eq(Projective(X("b"), None()), D(1)), All("t", PrimeType(), Eq(Projective(X("b"), Some(X("t"))), Chi(Add(X("b"), Cast(X("t")))))))));
    private static Formula NormNonzeroFormula() => PrimeBody(Alls([("b", FieldType()), ("t", PrimeType())],
        Imp(Ne(Pow(X("b"), X("p")), X("b")), Ne(NormQ(X("b"), Cast(X("t"))), D(0)))));
    private static Formula ExpansionFormula() => PrimeBody(Alls([("b", FieldType()), ("t", PrimeType())], Eq(
        NormQ(X("b"), Cast(X("t"))), Add(Add(Pow(Cast(X("t")), D(2)),
            Mul(Add(X("b"), Pow(X("b"), Pow(X("p"), D(2)))), Cast(X("t")))), Mul(X("b"), Pow(X("b"), Pow(X("p"), D(2))))))));
    private static Formula ProjectiveCrossFormula() => PrimeBody(Alls([("b", FieldType()), ("t", PrimeType()), ("s", PrimeType())],
        Imp(And(Ne(Pow(X("b"), X("p")), X("b")), Eq(Projective(X("b"), Some(X("t"))), Projective(X("b"), Some(X("s"))))),
            Eq(Mul(Pow(NormQ(X("b"), Cast(X("t"))), X("p")), NormQ(X("b"), Cast(X("s")))),
                Mul(NormQ(X("b"), Cast(X("t"))), Pow(NormQ(X("b"), Cast(X("s"))), X("p")))))));
    private static Formula PrimeFixedFormula() => PrimeBody(All("t", PrimeType(), Eq(Pow(Cast(X("t")), X("p")), Cast(X("t")))));
    private static Formula FiberFormula() => PrimeBody(Alls([("b", FieldType()), ("y", FieldType())],
        Imp(Ne(Pow(X("b"), X("p")), X("b")), LeqOf(Card(Filter(Call("Option", PrimeType()),
            Eq(Projective(X("b"), X("t")), X("y")))), D(2)))));

    private static Formula LeqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula NotOf(Formula a) => new Formula.Not(a);
    private static Formula GenericField(Formula body) => All("F", X("Type"), Instance(Call("Field", X("F")), body));
    private static Formula GenericChar(Formula body) => PrimeBody(GenericField(Instance(Call("CharP", X("F"), X("p")), body)));
    private static Formula Cast(Formula t) => Call("algebraMap", PrimeType(), FieldType(), t);
    private static Formula Some(Formula t) => App(Qualified("Option", "some"), t);
    private static Formula None() => Qualified("Option", "none");
    private static Formula Chi(Formula x) => Call("chi", X("p"), x);
    private static Formula NormQ(Formula b, Formula t) => Call("Q", X("p"), b, t);
    private static Formula Projective(Formula b, Formula t) => Call("projectiveClass", X("p"), b, t);
    private static Formula NormPoly(Formula B, Formula C, Formula t) => Call("normPoly", B, C, t);
    private static Formula Mate(Formula C, Formula t) => Call("projectiveMate", C, t);
    private static Formula Univs(Formula type) => Typed(Qualified("Finset", "univ"), Call("Finset", type));
    private static Formula Filter(Formula type, Formula pred) => App(Qualified("Finset", "filter"), LambdaOf("t", type, pred), Univs(type));
}

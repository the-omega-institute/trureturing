using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class SelfConjugateEvenPolynomialRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/klostermeyer2026nullspace");
    private static readonly LibraryNoteRef Invariants =
        LibraryNoteRef.Create("D5/L/ArithUnits/mattareipizzato2017reciprocal");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => F.Id("R");
    private static Formula X => F.Id("X");
    private static Formula Field => F.Id("F2");
    private static Formula Readings => F.Id("EvenReading");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every odd power of X^4+X^2 from the third onward obstructs the proposed sparse-power characterization.",
        H("Self-conjugate even polynomials and a uniform degree obstruction"),
        Blocks(
            Paragraph(Text("Throughout, R is the formal polynomial ring F2[X], X is its indeterminate, "
                + "C embeds a field element as a constant polynomial, comp denotes polynomial composition, "
                + "coeff denotes a coefficient, and support is the finite set of exponents with nonzero coefficients. "
                + "The notation natDegree is the natural degree used by Lean; every family member considered "
                + "below is nonzero. Equalities are formal polynomial equalities, rather than equalities of functions on F2.")),
            Node("F2", "The coefficient field", Equal(Field, Call("ZMod", F.D(2))),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Paragraph(Text("F2 is ZMod 2, the field with two elements. All coefficients and arbitrary "
                    + "constants in the representations below belong to this same field."))),
            Node("U", "The invariant base polynomial", Equal(F.Id("U"), Add(Pow(X, F.D(4)), Pow(X, F.D(2)))),
                AssessedProvenance.FromRepo(Source, Invariants), DescribeRole.Definition,
                Paragraph(Text("In characteristic two, (X+1)^2 = X^2+1 and (X+1)^4 = X^4+1. "
                    + "The two constant terms cancel, so U.comp(X+1)=U. Its highest term has coefficient one, "
                    + "and its degree is four. Also U=(X^2+X)^2. More generally, for any prime p and field K "
                    + "of characteristic p, with indeterminate T, the polynomials in K[T] fixed by "
                    + "translation T+1 are polynomials in T^p-T. This is the existing result in Section 5 "
                    + "of the second reference; the family calculation here uses Frobenius directly."))),
            Node("P", "The entire power family", All("r", N, Equal(Call("P", F.Id("r")), Pow(F.Id("U"), F.Id("r")))),
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition,
                Paragraph(Text("P is defined for every natural r, including zero. The obstruction uses every "
                    + "odd r at least three, without an upper bound. Composition preserves powers, hence every "
                    + "P(r) is fixed by translation by one. Monicity is preserved by powers, giving degree 4r."))),
            Node("FamilyEvent", "All simultaneous witness properties", FamilyFormula(),
                AssessedProvenance.FromRepo(Source, Invariants), DescribeRole.Definition,
                Paragraph(Text("FamilyEvent(r) contains all of the displayed clauses together. The no-representation "
                    + "clause quantifies over every c in F2, every natural m and every function k from Fin(m) to "
                    + "the naturals. Empty sums, repeated indices and k(i)=0 are included.")),
                Paragraph(Math(Disp(All("r", N, Imp(And(Call("Odd", F.Id("r")), Le(F.D(3), F.Id("r"))),
                    Call("FamilyEvent", F.Id("r"))))))),
                Paragraph(Text("For every odd natural r at least three these properties hold. To see the even-exponent "
                    + "clause, write P(r) as the expansion by two of (X^2+X)^r: expansion replaces X by X^2, "
                    + "so its coefficients vanish at odd exponents. Since r is positive, evaluation at zero "
                    + "is zero, which is also the constant coefficient and implies divisibility by X. "
                    + "Evaluation at one is zero because U(1)=1+1=0. Every nonzero coefficient in F2 is one, "
                    + "so evaluation at one equals the support cardinality cast into F2. Its vanishing gives "
                    + "even support cardinality. The degree 4r is even, and the reflection identity follows "
                    + "from -X=X in characteristic two.")),
                Paragraph(Text("The degree obstruction is uniform: odd r is coprime to 2 and therefore to every "
                    + "2^k for every natural k. If 4r=2^k, then r divides 2^k, forcing r=1, contrary to r at least three. "
                    + "Monicity gives coefficient one at exponent 4r. Each proposed powers-of-two monomial "
                    + "has coefficient zero there; an arbitrary constant also has coefficient zero because "
                    + "4r is positive. Finite addition preserves that zero coefficient, independently of "
                    + "cancellations or repeated indices. This contradicts formal polynomial equality."))),
            Node("EvenReading", "Six explicit conventional domains", null,
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition,
                Paragraph(Text("EvenReading has exactly six constructors: exponents, degree, support, "
                    + "zeroConstant, divisibleByX and reflection. The source does not define its word even. "
                    + "These alternatives describe the stated conventional readings without asserting a "
                    + "unique author-intended meaning. The zero-constant and X-divisibility alternatives "
                    + "are equivalent but are kept explicit."))),
            Node("Domain", "The domain belonging to each reading", DomainFormula(),
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition,
                Paragraph(Text("The six domain predicates respectively mean even supported exponents, even natural "
                    + "degree, even support cardinality, zero constant coefficient, divisibility by X, and "
                    + "invariance under reflection. Every eligible P(r) lies in their intersection. "
                    + "For this nonzero family, the natural degree is the ordinary polynomial degree."))),
            Node("SourceParity", "Both branches of the source parity rule", ParityFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Paragraph(Text("The phrase that X^0 is a term means that the constant coefficient of p is nonzero. "
                    + "SourceParity retains the implication to odd m in that case and the implication to even m "
                    + "otherwise. For the zero-constant family, this source rule would require even m. "
                    + "The contradiction already excludes all m before imposing this restriction."))),
            Node("DisplayedRepresentation", "The literal displayed representation", RepresentationFormula(false),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Paragraph(Text("This is exactly the finite sum displayed in Conjecture 2, together with its two "
                    + "prose parity branches. The indices are arbitrary naturals, with no distinctness or "
                    + "injectivity assumption. In particular, m=0 and exponent index zero remain allowed. "
                    + "The display has no separate constant term; its mention of a constant in prose is "
                    + "preserved by SourceParity rather than silently repaired."))),
            Node("ConstantRepresentation", "Separate optional-constant robustness", RepresentationFormula(true),
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition,
                Paragraph(Text("ConstantRepresentation adds an arbitrary c in F2 as C(c) while retaining the "
                    + "same source parity predicate. This explicitly labelled variant is broader than the "
                    + "literal display. The family excludes it even without the parity predicate; it is "
                    + "robustness of the same witnesses, rather than a replacement source assertion."))),
            Node("PublishedIff", "The complete universally quantified published iff", IffFormula(false),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Paragraph(Text("For each reading e, PublishedIff(e) quantifies over every formal polynomial p in R "
                    + "with Domain(e,p). It retains both directions of self-conjugacy if and only if the "
                    + "displayed representation, with both source parity branches inside that representation. "
                    + "No restriction to the power family is added to this universal assertion."))),
            Node("OptionalConstantIff", "The complete optional-constant variant", IffFormula(true),
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition,
                Paragraph(Text("This is the same universal iff with ConstantRepresentation on its right-hand side. "
                    + "Its optional constant is separate from the source display. Refuting the literal iff "
                    + "does not require identifying a corrected sufficient condition."))),
            Node("claim", "The disjunction of the complete interpretation alternatives", ClaimFormula(),
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition,
                Paragraph(Text("claim asserts that at least one of the six complete PublishedIff assertions or "
                    + "its optional-constant counterpart holds. It contains no assumption that any auxiliary "
                    + "family property is true. Its negation therefore refutes every complete alternative, "
                    + "rather than refuting a conjunction through an unrelated failed clause."))),
            Node("result", "Every complete alternative is false", new Formula.Not(F.Id("claim")),
                AssessedProvenance.FromRepo(Source, Invariants), DescribeRole.Theorem,
                Paragraph(Math(Disp(All("e", Readings, And(new Formula.Not(Call("PublishedIff", F.Id("e"))),
                    new Formula.Not(Call("OptionalConstantIff", F.Id("e")))))))),
                Paragraph(Text("For every odd r at least three and every reading e, FamilyEvent(r) supplies both "
                    + "Domain(e,P(r)) and self-conjugacy. A displayed representation would give the excluded "
                    + "optional-constant equality at c=0; a ConstantRepresentation would give it at its own c. "
                    + "Applying the necessary direction of either complete iff to this actual P(r) is "
                    + "therefore contradictory. This is a full source-iff bridge under each reading, not "
                    + "merely a failure of an auxiliary family condition. Taking r=3 discharges existence "
                    + "of a witness after the uniform argument, and refutes the existential disjunction claim.")),
                Paragraph(Text("The meaning intended by the author for even remains unverified. The refutation "
                    + "covers the six explicit conventional domains in the published unrestricted polynomial "
                    + "context; an added authoritative restriction excluding this family would require a "
                    + "different statement. The optional-constant result is separately identified robustness. "
                    + "Neither a unique semantic repair nor a new invariant-algebra mechanism is asserted."))))));

    private static DocumentBlock Node(string name, string title, Formula? formula,
        AssessedProvenance provenance, DescribeRole role, params DocumentBlock[] exposition) =>
        Describe.Lean(DescribeId.Create("self-conjugate-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(exposition), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("klostermeyer-self-conjugate-even-polynomial-conjecture-2"),
                ResolutionKind.Refuted) : null);

    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula domain) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, domain);
    private static Formula Divides(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula Conjunction(params Formula[] clauses) => clauses.Length == 1
        ? clauses[0] : And(clauses[0], Conjunction(clauses[1..]));
    private static Formula Invariant(Formula p) => Equal(Call("comp", p, Add(X, F.D(1))), p);
    private static Formula EvenExponents(Formula p) => All("n", N,
        Imp(Member(F.Id("n"), Call("support", p)), Call("Even", F.Id("n"))));
    private static Formula SparseSum(Formula m) => Seq(
        new Formula.Subscript(F.Sum, Member(F.Id("i"), Call("Fin", m))),
        Pow(X, Pow(F.D(2), Call("k", F.Id("i")))));
    private static Formula Indices(Formula m) => new Formula.TypeArrow(Call("Fin", m), N);

    private static Formula FamilyFormula()
    {
        var r = F.Id("r"); var p = Call("P", r); var m = F.Id("m");
        var exclusion = All("c", Field, All("m", N, All("k", Indices(m),
            NotEqual(p, Add(Call("C", F.Id("c")), SparseSum(m))))));
        return All("r", N, Iff(Call("FamilyEvent", r), Conjunction(
            NotEqual(p, F.D(0)), Call("Monic", p), Invariant(p), EvenExponents(p),
            Equal(Call("natDegree", p), Multiply(F.D(4), r)), Call("Even", Call("natDegree", p)),
            Equal(Call("coeff", p, F.D(0)), F.D(0)), Call("Even", Call("card", Call("support", p))),
            Divides(X, p), Equal(Call("comp", p, new Formula.Negate(X)), p), exclusion)));
    }

    private static Formula DomainFormula()
    {
        var p = F.Id("p");
        Formula D(string reading) => Call("Domain", F.Id(reading), p);
        return All("p", R, Conjunction(
            Iff(D("exponents"), EvenExponents(p)),
            Iff(D("degree"), Call("Even", Call("natDegree", p))),
            Iff(D("support"), Call("Even", Call("card", Call("support", p)))),
            Iff(D("zeroConstant"), Equal(Call("coeff", p, F.D(0)), F.D(0))),
            Iff(D("divisibleByX"), Divides(X, p)),
            Iff(D("reflection"), Equal(Call("comp", p, new Formula.Negate(X)), p))));
    }

    private static Formula ParityFormula()
    {
        var p = F.Id("p"); var m = F.Id("m"); var coeff = Call("coeff", p, F.D(0));
        return All("p", R, All("m", N, Iff(Call("SourceParity", p, m),
            And(Imp(NotEqual(coeff, F.D(0)), Call("Odd", m)),
                Imp(Equal(coeff, F.D(0)), Call("Even", m))))));
    }

    private static Formula RepresentationFormula(bool constant)
    {
        var p = F.Id("p"); var m = F.Id("m");
        var sum = SparseSum(m);
        var rhs = constant ? Add(Call("C", F.Id("c")), sum) : sum;
        var witness = Ex("m", N, Ex("k", Indices(m),
            And(Equal(p, rhs), Call("SourceParity", p, m))));
        return All("p", R, Iff(Call(constant ? "ConstantRepresentation" : "DisplayedRepresentation", p),
            constant ? Ex("c", Field, witness) : witness));
    }

    private static Formula IffFormula(bool constant)
    {
        var p = F.Id("p"); var e = F.Id("e");
        return All("e", Readings, Iff(Call(constant ? "OptionalConstantIff" : "PublishedIff", e),
            All("p", R, Imp(Call("Domain", e, p), Iff(Invariant(p),
                Call(constant ? "ConstantRepresentation" : "DisplayedRepresentation", p))))));
    }

    private static Formula ClaimFormula() => Iff(F.Id("claim"), Ex("e", Readings,
        Or(Call("PublishedIff", F.Id("e")), Call("OptionalConstantIff", F.Id("e")))));
}

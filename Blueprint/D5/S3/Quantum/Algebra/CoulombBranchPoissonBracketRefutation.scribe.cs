using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CoulombBranchPoissonBracketRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuantumContext/gledhillhanany2023poissoncoulomb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jacobi and reducedness rule out the proposed diagonal spinor Poisson brackets for the second E6 and truck families.",
        H("An obstruction to diagonal spinor Poisson brackets"),
        Blocks(
            Definition("is-poisson-bracket", "IsPoissonBracket", "A complex Poisson bracket",
                PoissonFormula(), AssessedProvenance.FromLiterature(Source),
                "For a commutative complex algebra R, br is additive and complex homogeneous in each argument, "
                    + "antisymmetric, a derivation in its second argument, and satisfies the cyclic Jacobi identity. "
                    + "Antisymmetry also gives the derivation rule in the first argument. These are the Poisson axioms "
                    + "in Gledhill–Hanany, arXiv:2210.02966v2, main.tex, line 2237."),
            Definition("spinor-brackets", "SpinorBrackets", "The diagonal spinor relations",
                SpinorFormula(), AssessedProvenance.FromLiterature(Source),
                "The functions sUp and sDn give N components of weights plus one and minus one under br h. "
                    + "A mixed bracket equals h to the natural power e on the diagonal and zero off the diagonal; "
                    + "brackets between components of the same charge vanish. The conditional expression is the "
                    + "Kronecker delta rule. These are the spinor relations and the unlisted vanishing brackets "
                    + "of main.tex, lines 1851–1856 and 2191–2197. No positivity of e or lower bound on N is imposed by this definition."),
            Definition("conj-e6", "ConjE6", "The second E6 family",
                E6Formula(), AssessedProvenance.FromLiterature(Source),
                "For every natural n at least three, the proposed spinor relations are required in a reduced "
                    + "commutative complex algebra, with h nonzero, two spinor families of dimension two to the "
                    + "power 2n, and exponent n minus one. The two algebraic structures are chosen along with R. "
                    + "The symbol letI indicates that the chosen structure is used in the following expression. "
                    + "The source gives this rank range at main.tex, line 1807, the spinor dimension at line 1843, "
                    + "and the bracket conjecture at lines 1845–1856. The formula retains the spinor conditions "
                    + "on a reduced coordinate algebra and omits the additional adjoint generators."),
            Definition("conj-truck", "ConjTruck", "The truck family",
                TruckFormula(), AssessedProvenance.FromLiterature(Source),
                "For every natural n at least two and every positive natural multiplicity σ, a reduced "
                    + "commutative complex algebra is required with the same nonzero weight element and spinor "
                    + "dimension, now with exponent n plus σ minus one. Subtraction in both family definitions "
                    + "is natural subtraction. The quiver range is given at main.tex, line 2149, and the spinor "
                    + "dimension and bracket conjecture at lines 2185–2197. Only the spinor consequences are imposed here."),
            Definition("claim", "claim", "Existence of at least one proposed family",
                Iff(Local("claim"), Or(Local("ConjE6"), Local("ConjTruck"))),
                AssessedProvenance.FromRepo(Source),
                "The proposition is the disjunction of the two universally quantified family statements. "
                    + "Thus it asserts the existence of all the required algebras for at least one family, "
                    + "with the algebra and bracket allowed to depend on the family parameters. It expresses "
                    + "necessary spinor conditions for the source's conjectures; it asserts neither the adjoint "
                    + "relations nor an identification of an arbitrary algebra satisfying them with a Coulomb branch."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Neither proposed family exists"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix a complex Poisson bracket on a reduced commutative complex algebra R. "
                            + "For each a, the map b ↦ br a b is a complex derivation, so it vanishes at zero "
                            + "and obeys the usual power rule. Antisymmetry and the right Leibniz rule give "
                            + "br (a*b) c = a*(br b c) + (br a c)*b.")),
                    Paragraph(Text(
                        "Suppose e is at least one and h, x, y, z, w satisfy br h x = x, br h y = −y, "
                            + "br x y = br z w = h^e, and br x w = br x z = 0. Write e = k+1. "
                            + "Antisymmetry gives br w x = 0 and br x h = −x. Jacobi on x, z, w then "
                            + "reduces to the power rule for br x (h^(k+1)). It gives the vanishing of "
                            + "the complex scalar k+1 times h^k*x. The scalar is explicitly the natural "
                            + "number k+1 cast to the complex numbers, and is nonzero. Cancelling it yields h^k*x = 0.")),
                    Paragraph(Text(
                        "Consequently br (h^k*x) y = 0. Expanding by the left Leibniz rule, substituting "
                            + "br x y = h^(k+1), and using antisymmetry and the power rule on br y (h^k) gives "),
                        Math(Equal(Add(Multiply(Power(V("h"), V("k")), Power(V("h"), Add(V("k"), D(1)))),
                            Multiply(new Formula.Negate(Multiply(CastNat(V("k"), V("R")),
                                Multiply(Power(V("h"), Subtract(V("k"), D(1))), V("y")))), V("x"))), Zero(V("R")))),
                        Text(". Here k is cast from the natural numbers to R, and k−1 is natural subtraction. "
                            + "Multiplying the correction term by h makes it zero: at k=0 its scalar coefficient "
                            + "is zero, while at k=m+1 it becomes the natural number m+1 cast to R times "
                            + "h^(m+1)*x*y, which vanishes by h^k*x = 0. Multiplying the expanded bracket "
                            + "identity by h and rearranging therefore gives h^(2*(k+1)) = 0. Reducedness "
                            + "makes every nilpotent element zero, so h = 0.")),
                    Paragraph(Text(
                        "For spinor relations with N at least two, choose the distinct indices i=0 and j=1 "
                            + "in Fin N, and put x=sUp i, y=sDn i, z=sUp j, w=sDn j. The weight relations "
                            + "give br h x = x and br h y = −y. The two diagonal mixed brackets give "
                            + "br x y = br z w = h^e; the off-diagonal mixed bracket and the equal-charge "
                            + "bracket give br x w = br x z = 0. Thus every such collection with e at least "
                            + "one forces h = 0.")),
                    Paragraph(Text(
                        "Apply the second E6 family statement at n=3: N=2^6=64 and e=2. The preceding "
                            + "argument gives h = 0, contrary to its required nonvanishing. Apply the truck "
                            + "family statement at n=2 and σ=1: N=2^4=16 and e=2, giving the same contradiction. "
                            + "Each side of the disjunction is therefore impossible, proving its negation. "
                            + "The obstruction concerns precisely the displayed normalized mixed brackets "
                            + "together with the vanishing equal-charge brackets in a reduced complex algebra; "
                            + "it does not require any adjoint-generator relations."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gledhill-hanany-2023-coulomb-branch-poisson-bracket-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PoissonFormula()
    {
        Formula a = V("a"), b = V("b"), c = V("c");
        Formula addLeft = All("a", V("R"), All("b", V("R"), All("c", V("R"),
            Equal(Br(Add(a, b), c), Add(Br(a, c), Br(b, c))))));
        Formula scaleLeft = All("c", Complexes(), All("a", V("R"), All("b", V("R"),
            Equal(Br(Smul(c, a), b), Smul(c, Br(a, b))))));
        Formula addRight = All("a", V("R"), All("b", V("R"), All("c", V("R"),
            Equal(Br(a, Add(b, c)), Add(Br(a, b), Br(a, c))))));
        Formula scaleRight = All("c", Complexes(), All("a", V("R"), All("b", V("R"),
            Equal(Br(a, Smul(c, b)), Smul(c, Br(a, b))))));
        Formula antisymmetry = All("a", V("R"), All("b", V("R"),
            Equal(Br(a, b), new Formula.Negate(Parenthesized(Br(b, a))))));
        Formula leibniz = All("a", V("R"), All("b", V("R"), All("c", V("R"),
            Equal(Br(a, Multiply(b, c)), Add(Multiply(Br(a, b), c), Multiply(b, Br(a, c)))))));
        Formula jacobi = All("a", V("R"), All("b", V("R"), All("c", V("R"),
            Equal(Add(Add(Br(a, Br(b, c)), Br(b, Br(c, a))), Br(c, Br(a, b))), Zero(V("R"))))));
        return All("R", TypeAny(), Instance(At(Qualified("CommRing"), V("R")),
            Instance(At(Qualified("Algebra"), Complexes(), V("R")), All("br", BracketType(),
                Iff(LocalCall("IsPoissonBracket", V("br")),
                    And(addLeft, And(scaleLeft, And(addRight, And(scaleRight,
                        And(antisymmetry, And(leibniz, jacobi)))))))))));
    }

    private static Formula SpinorFormula()
    {
        Formula alpha = Alpha, beta = Beta, h = V("h"), e = V("e");
        Formula upAlpha = At(V("sUp"), alpha), downAlpha = At(V("sDn"), alpha);
        Formula upBeta = At(V("sUp"), beta), downBeta = At(V("sDn"), beta);
        Formula index = FinOf(V("N"));
        Formula positive = All("α", index, Equal(Br(h, upAlpha), upAlpha));
        Formula negative = All("α", index, Equal(Br(h, downAlpha), new Formula.Negate(Parenthesized(downAlpha))));
        Formula mixed = All("α", index, All("β", index,
            Equal(Br(upAlpha, downBeta), At(Qualified("ite"), Equal(alpha, beta), Power(h, e), Zero(V("R"))))));
        Formula upper = All("α", index, All("β", index, Equal(Br(upAlpha, upBeta), Zero(V("R")))));
        Formula lower = All("α", index, All("β", index, Equal(Br(downAlpha, downBeta), Zero(V("R")))));
        Formula body = Iff(LocalCall("SpinorBrackets", V("br"), h, V("sUp"), V("sDn"), e),
            And(positive, And(negative, And(mixed, And(upper, lower)))));
        return All("R", TypeAny(), Instance(At(Qualified("CommRing"), V("R")),
            All("N", Naturals(), All("br", BracketType(), All("h", V("R"),
                All("sUp", Arrow(index, V("R")), All("sDn", Arrow(index, V("R")), All("e", Naturals(), body))))))));
    }

    private static Formula E6Formula() => Iff(Local("ConjE6"),
        All("n", Naturals(), Imp(LE(D(3), V("n")), FamilyBody(Subtract(V("n"), D(1))))));

    private static Formula TruckFormula() => Iff(Local("ConjTruck"),
        All("n", Naturals(), Imp(LE(D(2), V("n")), All("σ", Naturals(),
            Imp(LE(D(1), SigmaLower), FamilyBody(Subtract(Add(V("n"), SigmaLower), D(1))))))));

    private static Formula FamilyBody(Formula exponent)
    {
        Formula index = FinOf(Power(D(2), Multiply(D(2), V("n"))));
        Formula relations = And(LocalCall("IsPoissonBracket", V("br")),
            And(NotEqual(V("h"), Zero(V("R"))),
                LocalCall("SpinorBrackets", V("br"), V("h"), V("sUp"), V("sDn"), exponent)));
        Formula elements = Some("br", BracketType(), Some("h", V("R"),
            Some("sUp", Arrow(index, V("R")), Some("sDn", Arrow(index, V("R")), relations))));
        return Some("R", Qualified("Type"), Some("ringR", At(Qualified("CommRing"), V("R")),
            LetInstance(V("ringR"), Some("algR", At(Qualified("Algebra"), Complexes(), V("R")),
                LetInstance(V("algR"), And(At(Qualified("IsReduced"), V("R")), elements))))));
    }

    private static Formula V(string name) => name switch
    {
        "α" => Alpha,
        "β" => Beta,
        "σ" => SigmaLower,
        _ => F.Id(name)
    };
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
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Algebra",
        "CoulombBranchPoissonBracketRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula TypeAny() => Seq(Qualified("Type"), Star);
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula BracketType() => Arrow(V("R"), Arrow(V("R"), V("R")));
    private static Formula Br(Formula a, Formula b) => At(V("br"), a, b);
    private static Formula Zero(Formula type) => Typed(D(0), type);
    private static Formula CastNat(Formula value, Formula type) => Typed(At(Qualified("Nat", "cast"), value), type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula LetInstance(Formula value, Formula body) =>
        Seq(Qualified("letI"), Sp, Colon, Eq, Sp, value, Semi, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}

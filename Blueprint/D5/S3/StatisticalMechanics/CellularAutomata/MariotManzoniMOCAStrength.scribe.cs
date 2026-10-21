using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class MariotManzoniMOCAStrengthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/mariotmanzoni2022moca");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every three distinct columns in the binary array of mutually orthogonal bipermutive cellular automata contain each binary triple equally often.",
        H("Strength three of the Mariot–Manzoni array"),
        Blocks(
            Node("ca", "The no-boundary cellular automaton", CaFormula(),
                "Definition 1, p. 6: “Let n, d ∈ ℕ with d ≤ n, and let f : F₂ᵈ → F₂ be a d-variable Boolean function. A cellular automaton of length n, diameter d and local rule f is a mapping F : F₂ⁿ → F₂ⁿ⁻ᵈ⁺¹ defined for all x ∈ F₂ⁿ as: F(x₁, · · · , xₙ) = (f(x₁, · · · , x_d), f(x₂, · · · , x_{d+1}), · · · , f(x_{n−d+1}, · · · , xₙ)).” Here n = 2b and d = b + 1; Fin indices start at zero. Addition in ZMod 2 is XOR. Each Fin constructor carries the displayed value and its arithmetic bound proof.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsBipermutive", "Bipermutive local rules", BipermutiveFormula(),
                "Page 7: “Formally, a local rule f : F₂ᵈ → F₂ is called bipermutive if it is defined as f(x₁, · · · , x_d) = x₁ ⊕ ϕ(x₂, · · · , x_{d−1}) ⊕ x_d for all x ∈ F₂ᵈ, where ϕ : F₂ᵈ⁻² → F₂ is any function of the d−2 central variables.” The parameter b is d − 1, and b − 1 is natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("AreOrthogonal", "Orthogonality of two automata", OrthogonalFormula(),
                "Page 7: “we define two bipermutive CA F₁, F₂ : F₂²⁽ᵈ⁻¹⁾ → F₂ᵈ⁻¹ to be orthogonal (or equivalently they are OCA) if the corresponding Latin squares are orthogonal.” Equation (6), p. 6, requires unequal superposed pairs at distinct cells. The left half indexes rows and the right half indexes columns; Fin.append joins those halves.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsMOCA", "Mutually orthogonal cellular automata", MocaFormula(),
                "Page 7: “Accordingly, a family of k pairwise orthogonal bipermutive CA F₁, · · · , F_k will be called a set of k-MOCA (mutually orthogonal cellular automata).” The index set is Fin k.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mocaArray", "The juxtaposed binary array", ArrayFormula(),
                "Equation (7), p. 8: “the row of A indexed by (x, y) is equal to: A(x, y) = (F₁(x, y), F₂(x, y), · · · , F_k(x, y)).” Rows are functions Fin (b + b) → ZMod 2; columns are pairs in Fin k × Fin b. Thus there are 2^(2b) rows and kb columns.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsOrthogonalArray", "Binary orthogonal arrays", OaFormula(),
                "Page 6: “is a N × n array with entries from a set S with s elements such that, for any N × t subarray, each t-uple of Sᵗ occurs exactly λ = N/sᵗ times”. Here s = 2. An injective map selects t distinct columns; Fintype.card counts the rows of each pattern fiber. Nat.div denotes natural integer division. If there are fewer than t columns, there is no such selection.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The strength question", Disp(Iff(Named("claim"), ClaimBody())),
                "Section 5, p. 12: “The most natural open question remains whether our Theorem 1 is really a tight lower bound on the correlation immunity of the Boolean functions constructed through k-MOCA. If further experiments show that the lowest correlation immunity order is always at least 3, then it would be interesting to try refining Lemma 3, and prove that the binary OA obtained from a set of k-MOCA has always at least strength 3.” The proposition quantifies over every b, k and family of local rules, and asserts strength three for the array in Equation (7).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Every MOCA array has strength three", Disp(ClaimBody()),
                "Flip one input bit. A single column changes under its left endpoint flip. For three columns ordered by starting position, use the first left endpoint when the first two starts differ, the last right endpoint when only the last start differs, and the common left endpoint when all starts coincide. These flips reverse the triple XOR, even when columns repeat, without requiring orthogonality. For two distinct columns with different starts, the earlier left endpoint suffices. At equal starts, orthogonality makes the pair of complete output vectors a bijection, so summation can be reindexed and one output bit flipped. The seven nonconstant integer character sums of a three-column array therefore vanish. Expanding the three-bit indicator gives eight times each fiber cardinality equal to the number of rows, which yields the asserted natural quotient. The theorem asserts strength three; sharpness and the corresponding Boolean-function statement are outside its conclusion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("moca-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula QCall(string owner, string name, params Formula[] arguments) => App(Qualified(owner, name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bit() => Call("ZMod", D(2));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Prod(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Proj(Formula x, byte n) => Seq(x, Dot, D(n));
    private static Formula Mk(Formula value) => Seq(Langle, Sp, value, Comma, Sp, Named("by"), Sp, Named("omega"), Sp, Rangle);
    private static Formula Rule(Formula b) => Arrow(Arrow(Fin(Add(b, D(1))), Bit()), Bit());
    private static Formula Family(Formula b, Formula k) => Arrow(Fin(k), Rule(b));
    private static Formula Rows(Formula b) => Arrow(Fin(Add(b, b)), Bit());
    private static Formula Columns(Formula b, Formula k) => Prod(Fin(k), Fin(b));
    private static Formula Parameters(Formula body, bool family = false)
    {
        Formula b = F.Id("b"), k = F.Id("k");
        return All("b", Nat(), family ? All("k", Nat(), All("f", Family(b, k), body)) : All("f", Rule(b), body));
    }

    private static Formula CaFormula()
    {
        Formula b = F.Id("b"), f = F.Id("f"), x = F.Id("x"), j = F.Id("j"), t = F.Id("t");
        Formula window = Fun("t", Fin(Add(b, D(1))),
            App(x, Mk(Add(Call("val", j), Call("val", t)))));
        Formula rhs = Fun("j", Fin(b), App(f, window));
        return Disp(Parameters(All("x", Rows(b), Eqn(Call("ca", b, f, x), Parenthesized(rhs)))));
    }

    private static Formula BipermutiveFormula()
    {
        Formula b = F.Id("b"), f = F.Id("f"), y = F.Id("y"), t = F.Id("t"), phi = F.Id("phi");
        Formula middle = Fun("t", Fin(Sub(b, D(1))), App(y, Mk(Add(Call("val", t), D(1)))));
        Formula rhs = Ex("phi", Arrow(Arrow(Fin(Sub(b, D(1))), Bit()), Bit()),
            All("y", Arrow(Fin(Add(b, D(1))), Bit()),
                Eqn(App(f, y), Add(Add(App(y, Mk(D(0))), App(phi, middle)), App(y, Mk(b))))));
        return Disp(Parameters(Iff(Call("IsBipermutive", b, f), rhs)));
    }

    private static Formula OrthogonalFormula()
    {
        Formula b = F.Id("b"), f = F.Id("f"), g = F.Id("g"), r = F.Id("r"), c = F.Id("c"), u = F.Id("u"), v = F.Id("v");
        Formula joined = QCall("Fin", "append", r, c), other = QCall("Fin", "append", u, v);
        Formula rhs = Imp(Ne(Pair(r, c), Pair(u, v)),
            Ne(Pair(Call("ca", b, f, joined), Call("ca", b, g, joined)),
                Pair(Call("ca", b, f, other), Call("ca", b, g, other))));
        foreach (string name in new[] { "v", "u", "c", "r" }) rhs = All(name, Arrow(Fin(b), Bit()), rhs);
        return Disp(Parameters(All("g", Rule(b), Iff(Call("AreOrthogonal", b, f, g), rhs))));
    }

    private static Formula MocaFormula()
    {
        Formula b = F.Id("b"), k = F.Id("k"), f = F.Id("f"), i = F.Id("i"), h = F.Id("h");
        Formula rhs = And(All("i", Fin(k), Call("IsBipermutive", b, App(f, i))),
            All("i", Fin(k), All("h", Fin(k), Imp(Ne(i, h), Call("AreOrthogonal", b, App(f, i), App(f, h))))));
        return Disp(Parameters(Iff(Call("IsMOCA", b, k, f), rhs), true));
    }

    private static Formula ArrayFormula()
    {
        Formula b = F.Id("b"), k = F.Id("k"), f = F.Id("f"), x = F.Id("x"), c = F.Id("c");
        Formula rhs = Fun("x", Rows(b), Fun("c", Columns(b, k), Call("ca", b, App(f, Proj(c, 1)), x, Proj(c, 2))));
        return Disp(Parameters(Eqn(Call("mocaArray", b, k, f), Parenthesized(rhs)), true));
    }

    private static Formula OaFormula()
    {
        Formula r = F.Id("R"), c = F.Id("C"), a = F.Id("A"), t = F.Id("t"), cols = F.Id("cols"), v = F.Id("v"), x = F.Id("r"), s = F.Id("s");
        Formula fiber = Seq(OpenBrace, Sp, x, Colon, Sp, r, Sp, Slash, Slash, Sp,
            Parenthesized(All("s", Fin(t), Eqn(App(a, x, App(cols, s)), App(v, s)))), Sp, CloseBrace);
        Formula count = Eqn(QCall("Fintype", "card", fiber),
            QCall("Nat", "div", QCall("Fintype", "card", r), new Formula.Power(D(2), t)));
        Formula rhs = All("cols", Arrow(Fin(t), c), Imp(QCall("Function", "Injective", cols), All("v", Arrow(Fin(t), Bit()), count)));
        Formula body = All("A", Arrow(r, Arrow(c, Bit())), All("t", Nat(),
            Iff(Call("IsOrthogonalArray", a, t), rhs)));
        return Disp(All("R", Named("Type"), All("C", Named("Type"),
            Seq(OpenBracket, Call("Fintype", r), CloseBracket, body))));
    }

    private static Formula ClaimBody()
    {
        Formula b = F.Id("b"), k = F.Id("k"), f = F.Id("f");
        return Parameters(Imp(Call("IsMOCA", b, k, f), Call("IsOrthogonalArray", Call("mocaArray", b, k, f), D(3))), true);
    }
}

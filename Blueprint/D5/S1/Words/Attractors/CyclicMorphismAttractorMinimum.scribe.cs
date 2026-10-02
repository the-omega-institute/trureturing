using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Attractors;

internal sealed class CyclicMorphismAttractorMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/gheeraertromanastipulanti2023attractors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cyclic morphism prefixes have the unrestricted attractor minimum of Conjecture 42.",
        H("String attractors of cyclically maximal morphisms"),
        Blocks(
            Paragraph(Text("Gheeraert, Romana and Stipulanti's Conjecture 42 concerns the original alphabet and every positive prefix length. Coefficients may vanish except at the first and last letters. Cyclic maximality is weak: equal rotations, proper powers, and unary primitive roots are included. The source is arXiv:2302.13647v2; published suppliers and the proved finite bridges are identified individually.")),
            Def("cyclicMorphism", "Original substitution", "For every natural k, proof hk of 0 < k, coefficient function c : Fin k → Nat and letter a : Fin k, cyclicMorphism hk c a is the list consisting of c(a) copies of the original letter 0 followed by the singleton letter a+1 if a.val+1 < k. Otherwise it is exactly c(a) copies of 0. The latter branch contains no appended letter. This is the substitution in Definition 2 of arXiv:2302.13647v2.", AssessedProvenance.FromLiterature(Source)),
            Def("cyclicDigit", "Periodic coefficient digit", "For every k, c : Fin k → Nat and a : Fin k, cyclicDigit c a equals c(a)-1 when a.val+1=k, and c(a) otherwise. Subtraction is natural-number subtraction. This represents the coefficient word in Proposition 34(3); positivity of the last coefficient makes natural decrement agree with the source integer decrement.", AssessedProvenance.FromLiterature(Source)),
            Def("cyclicNext", "Original cyclic phase", "For every k with hk : 0 < k and a : Fin k, cyclicNext hk a is the original letter with value (a.val+1) modulo k, with its Fin k bound certified by hk.", AssessedProvenance.FromRepo(Source)),
            Def("CyclicMaximal", "Weak cyclic maximum", "For every k and c : Fin k → Nat, form the length-k list d=List.ofFn(cyclicDigit c), in increasing original-letter order. CyclicMaximal c means: for every natural rotation amount r, d.rotate r is lexicographically less than or equal to d. Equality is allowed; no primitivity condition is imposed. This is the condition in Proposition 34(3).", AssessedProvenance.FromLiterature(Source)),
            Def("cyclicWord", "Literal substitution iterate", "For every k with hk : 0 < k, c : Fin k → Nat and natural n, cyclicWord hk c n is morphismPower (cyclicMorphism hk c) n [0], a list of original Fin k letters. The zero iterate is the singleton [0]. This is the iterate u_n of Definition 2.", AssessedProvenance.FromLiterature(Source)),
            Def("cyclicLength", "Original iterate length", "For every k with hk : 0 < k, c : Fin k → Nat and natural n, cyclicLength hk c n is the length of cyclicWord hk c n. Write this length as U(n). This is U_n of Definition 2.", AssessedProvenance.FromLiterature(Source)),
            Def("cyclicPrefix", "Same fixed-point prefix", "For every k with hk : 0 < k, c : Fin k → Nat and natural m, cyclicPrefix hk c m is (cyclicWord hk c m).take m. This is a finite definition, with no growth or fixed-point premise. Under the hypotheses of cyclic_iterate_structure its length is exactly m and it agrees with take m of every sufficiently long iterate.", AssessedProvenance.FromRepo(Source)),
            Def("cyclicInterior", "Original-letter interior", "For every k with hk : 0 < k and c : Fin k → Nat, cyclicInterior hk c is a function Nat → Fin k → List (Fin k). Its value at (0,a) is the empty list. Its value at (n+1,a) is wordPower (cyclicDigit c a) (cyclicWord hk c n), concatenated with cyclicInterior hk c n (cyclicNext hk a). Here wordPower j v concatenates j copies of v.", AssessedProvenance.FromRepo(Source)),
            Def("cyclicSegment", "Finite periodic digit segment", "For every k with hk : 0 < k, c : Fin k → Nat, natural n and a : Fin k, cyclicSegment hk c n a is the length-n list whose position i : Fin n is cyclicDigit c at the original letter (a.val+i.val) modulo k.", AssessedProvenance.FromRepo(Source)),
            Def("cyclicBlockProduct", "Original coefficient blocks", "For every k with hk : 0 < k, c : Fin k → Nat, naturals n,count and proof hcount : count ≤ k, cyclicBlockProduct hk c n count hcount is the flattened list of blocks indexed by a : Fin count in increasing order. Block a is wordPower (c(a)) (cyclicWord hk c (n-1-a.val)), with a embedded into Fin k using hcount. All differences are natural-number subtraction. This is the block expression in Proposition 4, represented by a finite indexed list and flattening.", AssessedProvenance.FromLiterature(Source)),
            Def("CyclicAttractorMinimum", "Complete minimum proposition", "For every k with hk : 0 < k and c : Fin k → Nat, CyclicAttractorMinimum hk c means: for every natural m with 0 < m, both clauses hold. First, for every natural i with i ≤ k-2, U(i) ≤ m and m < U(i+1), gamma(cyclicPrefix hk c m)=i+1. Second, U(k-1) ≤ m implies gamma(cyclicPrefix hk c m)=k. These are implications for all m and i; the definition adds no coefficient, rotation or primitivity hypotheses. This proposition records the full assertion of Conjecture 42; the definition supplies no proof of it.", AssessedProvenance.FromLiterature(Source)),
            Proof("cyclic_iterate_structure", "Nesting and stable prefix semantics", "For every natural k with hk : 2 ≤ k and c : Fin k → Nat with 1 ≤ c(0) and 1 ≤ c(k-1), the following six conclusions hold without a cyclic-maximality premise. For every natural n and letter a : Fin k, morphismPower (cyclicMorphism hk0 c) n [a] equals cyclicInterior hk0 c n a followed by the singleton original letter (a.val+n) modulo k, where hk0 certifies 0 < k. For every n, cyclicWord hk0 c n is a prefix of cyclicWord hk0 c (n+1), and U(n) < U(n+1). For every n, n+1 ≤ U(n). The function n ↦ U(n+1)-U(n) is monotone. Finally, for every naturals m,n with m ≤ U(n), cyclicPrefix hk0 c m equals (cyclicWord hk0 c n).take m. These nesting and unbounded-length statements identify the finite presentation with every original fixed-point prefix. Definition 2 and the working hypotheses supply the published fixed-point setting. The six-clause finite presentation, including the original-letter interior, growth gaps and prefix-stability bridge, is proved here.", AssessedProvenance.FromRepo(Source)),
            Proof("cyclic_fractional_prefix", "All-level fractional prefixes", "For every k with hk : 2 ≤ k, c : Fin k → Nat with 1 ≤ c(0), 1 ≤ c(k-1), CyclicMaximal c, and every natural n, (cyclicWord hk0 c (n+1)).dropLast is a prefix of wordPower (c(0)+1) (cyclicWord hk0 c n). Here hk0 certifies 0 < k. The assertion is about literal original-letter lists at every level. Weak rotation comparison includes equal rotations, arbitrary zero middle coefficients, proper powers and unary primitive roots. The fractional-prefix implication is published as Proposition 34(3 implies 1). This finite formulation additionally gives the explicit c(0)+1 power cap by an original-letter induction; it is a proved supplier of the full result.", AssessedProvenance.FromRepo(Source)),
            Proof("cyclic_word_recurrence", "Short and full original recurrences", "For every k with hk : 2 ≤ k and c : Fin k → Nat with 1 ≤ c(0) and 1 ≤ c(k-1), two identities hold without cyclic maximality. For every natural n with hn : n < k, cyclicWord hk0 c n equals cyclicBlockProduct hk0 c n n hn.le concatenated with the singleton original letter n : Fin k. For every natural n with k ≤ n, cyclicWord hk0 c n equals cyclicBlockProduct hk0 c n k le_rfl. Here hk0 certifies 0 < k; these use all original coefficient blocks, including zero multiplicities. Both identities are the published recurrences of Proposition 4, proved here for the original substitution rather than assumed.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The full original Conjecture 42 minimum"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural k with 2 ≤ k, coefficient function c : Fin k → Nat with c(0) ≥ 1 and c(k-1) ≥ 1, and CyclicMaximal c, for every natural m > 0: for every natural i ≤ k-2 with U(i) ≤ m < U(i+1), gamma(cyclicPrefix hk0 c m)=i+1; and if U(k-1) ≤ m, gamma(cyclicPrefix hk0 c m)=k. Here hk0 certifies 0 < k, U(n)=cyclicLength hk0 c n, and gamma minimizes over all eligible finite subsets of original positions with equal occurrences wholly inside the same prefix. The original alphabet, arbitrary zero middle coefficients, equality of rotations, proper powers, unary primitive roots and all positive prefix lengths remain in scope. The endpoint intervals and full-k residual scan construct the upper bound; unrestricted singleton factors give the matching lower bound. The proof includes r=0, empty residual intervals and the terminal scan level. No paper statement is a premise."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("parry-string-attractor-minimum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Def(string name, string title, string prose, AssessedProvenance provenance) =>
        Node(name, title, prose, DescribeRole.Definition, provenance);
    private static DocumentBlock Proof(string name, string title, string prose, AssessedProvenance provenance) =>
        Node(name, title, prose, DescribeRole.Theorem, provenance);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ResultFormula()
    {
        Formula k = F.Id("k"), c = F.Id("c"), m = F.Id("m"), i = F.Id("i");
        Formula hypotheses = And(AtMost(D(2), k), And(AtMost(D(1), Call("coefficient", c, D(0))),
            And(AtMost(D(1), Call("coefficient", c, Minus(k, D(1)))), Call("CyclicMaximal", c))));
        Formula early = All("i", Naturals(), Implies(And(AtMost(i, Minus(k, D(2))),
            And(AtMost(Call("cyclicLength", c, i), m), Less(m, Call("cyclicLength", c, Plus(i, D(1)))))),
            Equal(Call("gamma", Call("cyclicPrefix", c, m)), Plus(i, D(1)))));
        Formula late = Implies(AtMost(Call("cyclicLength", c, Minus(k, D(1))), m),
            Equal(Call("gamma", Call("cyclicPrefix", c, m)), k));
        return Disp(All("k", Naturals(), All("c", Call("Function", Call("Fin", k), Naturals()),
            Implies(hypotheses, All("m", Naturals(), Implies(Less(D(0), m), And(early, late)))))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Minus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}

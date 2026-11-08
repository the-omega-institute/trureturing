using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FrobeniusCharacterDegreesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026finitecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-point-free conjugation constrains simple complex degrees, with a trace-rigidity bridge for nonabelian kernels.",
        H("Degrees over normal subgroups"),
        Blocks(Node("degree_square_le_card", "The degree-square bound", Square(),
            "The group algebra maps onto the endomorphism algebra of a simple representation. Comparing dimensions bounds the square of its degree by the group order."),
            Node("degree_dvd_or_index_dvd_of_fixedPointFree", "The divisibility dichotomy", Dichotomy(),
            "A nontrivial simple constituent of the restriction has inertia subgroup equal to the normal subgroup. Clifford decomposition then makes the subgroup index divide the degree. A trivial constituent makes the representation descend to the quotient, where its degree divides the quotient order."),
            Node("trivial_of_character_invariant_fixedPointFree", "Character invariance forces triviality", CharacterInvariant(),
            "Assume a simple representation has character invariant under a fixed-point-free automorphism. Character orthogonality supplies an isomorphism with the twisted representation, hence an invertible intertwiner. Surjectivity of the Lang map makes its twisted traces constant. Density extends the resulting trace identities to every endomorphism, and rank-one trace pairings force the representation to be trivial."),
            Node("degree_dvd_or_index_dvd_of_fixedPointFree_nonabelian", "The nonabelian divisibility dichotomy", DichotomyNonabelian(),
            "The same Clifford argument works for an arbitrary finite normal subgroup. Character invariance under an inertia conjugation is first converted to triviality by the trace-rigidity theorem, so a nontrivial constituent has inertia exactly the kernel; the two Clifford branches give the stated divisibility alternatives."),
            ModularEquivNode(), ModularCharacterNode(), ModularAlternativeNode())));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("frobenius-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/FiniteGroups/FrobeniusCharacterDegrees." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Square()
    {
        Formula g = F.Id("G"), x = F.Id("X");
        return Group("G", All("X", App(F.Id("FDRep"), Complex(), g),
            Instance(App(Q("CategoryTheory", "Simple"), x),
                new Formula.Relation(new Formula.Power(Degree(x), D(2)), FormulaRelationOperator.LessThanOrEqual,
                    App(Q("Nat", "card"), g)))));
    }
    private static Formula Dichotomy()
    {
        Formula k = F.Id("K"), n = F.Id("N"), g = F.Id("g"), v = F.Id("n"), w = F.Id("W");
        Formula fixedFree = All("g", k, Imp(new Formula.Not(Member(g, n)),
            All("n", n, Imp(Equal(App(Q("MulAut", "conjNormal"), g, v), v), Equal(v, D(1))))));
        Formula index = App(Q("Subgroup", "index"), n);
        Formula conclusion = new Formula.Logic(Parenthesized(Divides(Degree(w), index)), FormulaLogicOperator.Or,
            Parenthesized(Divides(index, Degree(w))));
        return Group("K", All("N", App(F.Id("Subgroup"), k),
            Instance(App(Q("Subgroup", "Normal"), n), Instance(App(F.Id("IsMulCommutative"), n),
                Imp(fixedFree, All("W", App(F.Id("FDRep"), Complex(), k),
                    Instance(App(Q("CategoryTheory", "Simple"), w), conclusion)))))));
    }

    private static Formula CharacterInvariant()
    {
        Formula a = F.Id("A"), alpha = F.Id("alpha"), v = F.Id("V"), x = F.Id("a");
        Formula rho = new Formula.Apply(Seq(Operatorname, Grp(F.Id("FDRep")), Dot, Rho), [v]);
        Formula fixedFree = All("a", a, Imp(Equal(App(alpha, x), x), Equal(x, D(1))));
        Formula invariant = All("a", a,
            Equal(App(Q("FDRep", "character"), v, App(alpha, x)),
                App(Q("FDRep", "character"), v, x)));
        Formula simple = App(Q("CategoryTheory", "Simple"), v);
        Formula trivial = App(Q("Representation", "IsTrivial"), rho);
        return Group("A", All("alpha", App(F.Id("MulAut"), a),
            Imp(fixedFree, All("V", App(F.Id("FDRep"), Complex(), a),
                Instance(simple, Imp(invariant, trivial))))));
    }

    private static Formula DichotomyNonabelian()
    {
        Formula k = F.Id("K"), n = F.Id("N"), g = F.Id("g"), v = F.Id("n"), w = F.Id("W");
        Formula fixedFree = All("g", k, Imp(new Formula.Not(Member(g, n)),
            All("n", n, Imp(Equal(App(Q("MulAut", "conjNormal"), g, v), v), Equal(v, D(1))))));
        Formula index = App(Q("Subgroup", "index"), n);
        Formula conclusion = new Formula.Logic(Parenthesized(Divides(Degree(w), index)), FormulaLogicOperator.Or,
            Parenthesized(Divides(index, Degree(w))));
        return Group("K", All("N", App(F.Id("Subgroup"), k),
            Instance(App(Q("Subgroup", "Normal"), n),
                Imp(fixedFree, All("W", App(F.Id("FDRep"), Complex(), k),
                    Instance(App(Q("CategoryTheory", "Simple"), w), conclusion))))));
    }
    private static Formula Group(string name, Formula body) => All(name, F.Id("Type"),
        Instance(App(F.Id("Group"), F.Id(name)), Instance(App(F.Id("Finite"), F.Id(name)), body)));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Degree(Formula v) => App(Q("Module", "finrank"), Complex(), v);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static DocumentBlock ModularEquivNode() => Node(
        "trivial_of_equiv_fixedPointFree_of_isAlgClosed",
        "Twist equivalence forces trivial action in every characteristic", ModularRigidity(false),
        "Let k be algebraically closed and A finite. The displayed e is an actual equivalence between the simple finite-dimensional representation and its twist; equality of traces is not substituted for this hypothesis. Its invertible intertwiner T satisfies T rho(a) = rho(alpha(a)) T. The fixed-point-free commutator map is surjective, so cyclic invariance of trace makes tr(T rho(a)) constant. Applying this also to products, and extending linearly through k[A], gives tr(U (T rho(a) - T)) = 0 for every endomorphism U, by density. Rank-one endomorphisms detect every vector under the trace pairing in every characteristic. Thus T rho(a) = T, and injectivity of T proves trivial action. This is the repository's derivation from classical density and the fixed-point-free commutator lemma; no novelty or characteristic-zero argument is claimed.");

    private static DocumentBlock ModularCharacterNode() => Node(
        "trivial_of_character_invariant_fixedPointFree_of_isAlgClosed",
        "Invariant simple characters give trivial action in every characteristic", ModularRigidity(true),
        "Here FDRep packages finite dimensionality and Simple V supplies irreducibility. The character hypothesis is pointwise on every a in A. Twisting by the automorphism preserves irreducibility, and simple-character separation over the algebraically closed field turns this hypothesis into a genuine equivalence with the twist. The preceding intertwiner and density argument then proves triviality. This repository derivation uses ordinary k-valued characters of simple modules; it uses neither division by the group order nor characteristic-zero orthogonality. The earlier complex theorem and its complex divisibility consequences retain their stated scopes.");

    private static DocumentBlock ModularAlternativeNode() => Node(
        "trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed",
        "A structural Frobenius alternative over an algebraically closed field", ModularAlternative(),
        "Let K be a finite group and N a normal subgroup, with every conjugation by an element outside N fixing only the identity of N. Clifford restriction chooses a simple N-constituent V and a multiplicity e. For a nontrivial V, membership in its inertia subgroup is equivalent to an isomorphism with the conjugate constituent. The existing FDRep-isomorphism/representation-equivalence bridge gives the twist equivalence, so fixed-point-free rigidity excludes every inertia element outside N. Since N lies in the inertia group, inertia equals N and the orbit has N.index elements. The generic Clifford formula is an equality of natural numbers: finrank_k W = e * inertia.index * finrank_k V. It therefore gives N.index dividing finrank_k W, with witness e * finrank_k V. In the trivial-constituent branch, every conjugate constituent has trivial action, hence so does the product module defining the Clifford sum. The actual Clifford isomorphism, the shrink equivalence and injectivity transport trivial action back to the restriction of W. This branch uses no character-equals-dimension test. In characteristic p the trace of the identity is only the image of the natural-number dimension in k: p and zero have the same image. Such field-valued equalities cannot certify natural-number divisibility or the converse implication from constant character to triviality for arbitrary modules (p copies of a module already have zero character). The surviving arithmetic statement comes from the natural-number Clifford formula. This result does not replace trivial restriction by the assertion that finrank_k W divides N.index in positive characteristic. The four earlier complex results, including their full integer degree dichotomies, remain separate. Density, Clifford theory and this synthesis are classical mathematics, not a claim of literature novelty.");

    private static Formula ModularRigidity(bool characterHypothesis)
    {
        Formula k = F.Id("k"), a = F.Id("A"), alpha = F.Id("alpha"), v = F.Id("V"), x = F.Id("a");
        Formula rho = ModularRho(v);
        Formula fixedFree = All("a", a, Imp(Equal(App(alpha, x), x), Equal(x, D(1))));
        Formula conclusion = App(Q("Representation", "IsTrivial"), rho);
        Formula hypothesis = characterHypothesis
            ? All("a", a, Equal(App(Q("FDRep", "character"), v, App(alpha, x)),
                App(Q("FDRep", "character"), v, x)))
            : App(Q("Representation", "Equiv"), rho,
                App(Seq(rho, Dot, Operatorname, Grp(F.Id("comp"))), App(Q("MulAut", "toMonoidHom"), alpha)));
        return All("k", MTypeStar(), Instance(App(F.Id("Field"), k),
            Instance(App(F.Id("IsAlgClosed"), k),
            All("A", MTypeStar(), Instance(App(F.Id("Group"), a), Instance(App(F.Id("Finite"), a),
            All("alpha", App(F.Id("MulAut"), a), All("hAlpha", fixedFree,
            All("V", App(F.Id("FDRep"), k, a), Instance(App(Q("CategoryTheory", "Simple"), v),
            All(characterHypothesis ? "hChi" : "e", hypothesis, conclusion)))))))))));
    }

    private static Formula ModularAlternative()
    {
        Formula k = F.Id("k"), group = F.Id("K"), n = F.Id("N"), g = F.Id("g"), x = F.Id("n"), w = F.Id("W");
        Formula fixedFree = All("g", group, Imp(new Formula.Not(Member(g, n)),
            All("n", n, Imp(Equal(App(Q("MulAut", "conjNormal"), g, x), x), Equal(x, D(1))))));
        Formula restriction = App(Seq(ModularRho(w), Dot, Operatorname, Grp(F.Id("comp"))),
            App(Q("Subgroup", "subtype"), n));
        Formula conclusion = new Formula.Logic(
            Parenthesized(App(Q("Representation", "IsTrivial"), restriction)), FormulaLogicOperator.Or,
            Parenthesized(Divides(App(Q("Subgroup", "index"), n), App(Q("Module", "finrank"), k, w))));
        return All("k", MTypeStar(), Instance(App(F.Id("Field"), k), Instance(App(F.Id("IsAlgClosed"), k),
            All("K", F.Id("Type"), Instance(App(F.Id("Group"), group), Instance(App(F.Id("Finite"), group),
            All("N", App(F.Id("Subgroup"), group), Instance(App(Q("Subgroup", "Normal"), n),
            All("hfix", fixedFree, All("W", App(F.Id("FDRep"), k, group),
            Instance(App(Q("CategoryTheory", "Simple"), w), conclusion)))))))))));
    }

    private static Formula MTypeStar() => Seq(F.Id("Type"), Star);
    private static Formula ModularRho(Formula v) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("FDRep")), Dot, Rho), [v]);
}

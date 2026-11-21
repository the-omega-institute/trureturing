using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Quandles;

internal sealed class GenevoisQ94SettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.";
    private const string Question =
        "In a quandle product, is the intersection between two arbitrary parabolic subgroups again a parabolic subgroup?";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/genevois2025quandleproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two conjugates of the upper factor in a two-factor quandle product have a nonparabolic intersection.",
        H("An intersection of parabolics in a two-factor quandle product"),
        Blocks(
            Node("Oposet", "The orthogonality relation of an oposet",
                OrderedIndices(HasType(Call("Oposet", I), F.Id("Type"))),
                "Definition 2.1 supplements the supplied partial order on I with a symmetric, irreflexive "
                + "binary relation on I. Orthogonality implies incomparability in both directions. If i ≤ j "
                + "and j is orthogonal to k, then i is orthogonal to k."),
            Node("LowerIndex", "Indices strictly below a given index",
                OrderedIndices(All("k", I, EqTo(Below(F.Id("k")),
                    SetBuilder("i", I, new Formula.Relation(F.Id("i"), FormulaRelationOperator.LessThan, F.Id("k")))))),
                "The subtype uses the strict order of I. Its elements keep the proof that their index is below k."),
            Node("LowerAction", "The action on the groupoid below an index",
                Family(All("k", I, HasType(Call("LowerAction", G, F.Id("k")), F.Id("Type")))),
                "A lower action consists of a homomorphism onIndex from G(k) to the permutations of LowerIndex(k). "
                + "For each b in G(k) and i below k, onFactor gives a multiplicative equivalence from G(i) "
                + "to G(onIndex(b)(i)), where the underlying index of each subtype element is used. "
                + "The identity acts as the identity on the dependent disjoint union. Acting by bc equals "
                + "acting first by c and then by b, as an equality in that union."),
            Node("LowerAction.apply", "Applying a lower action",
                ApplyFormula(),
                "Here apply denotes LowerAction.apply. The output is the dependent pair of the permuted lower index and the image of the factor element "
                + "under onFactor. Its type is the disjoint union indexed by LowerIndex(k)."),
            Node("PreservesOrder", "Order preservation of a lower action",
                OrderFormula(),
                "For each acting element b, the index permutation both preserves and reflects the induced order."),
            Node("IsQuandleAction", "The three-index quandle law",
                QuandleLawFormula(),
                "The family A includes an action at every index and is supplied with order preservation at every index. "
                + "For i < j < k and a, b, c in the corresponding factors, c acts on the output of b acting on a. "
                + "On the other side, c acts on both b and a, and the resulting element from b acts on the resulting "
                + "element from a. Order preservation at k gives the required strict inequality between their image indices. "
                + "The equality compares the two dependent pairs in the disjoint union over I."),
            Node("QuandleSystem", "A quandle system with nontrivial factors",
                Family(HasType(Call("QuandleSystem", I, G), F.Id("Type"))),
                "Definition 2.4 combines an oposet on I with one lower action at each index for the supplied family "
                + "of groups. Every index permutation preserves and reflects order and orthogonality. "
                + "The actions satisfy the three-index quandle law. Each factor is nontrivial by the convention on p. 9."),
            Node("relators", "The relators in the indexed free product",
                RelatorsFormula(),
                "The map u(i,a) is the free-product inclusion of a from G(i). The term w(S,b,i,a) is the free-product image "
                + "of the dependent pair obtained when b acts on a at the strictly lower index i. "
                + "Each relation contributes its left-hand side times the inverse of its right-hand side."),
            Node("QuandleProduct", "The normal-closure quotient",
                System(EqTo(Product(), Seq(FreeProduct(), Slash, Call("normalClosure", Call("relators", S))))),
                "Definition 2.4 imposes the orthogonal commutations and twists by quotienting the indexed free "
                + "product by the normal closure of the full relator set."),
            Node("factor", "The maps of the factors into the quotient",
                System(All("i", I, All("a", Factor(F.Id("i")),
                    EqTo(Call("factor", S, F.Id("i"), F.Id("a")),
                        Call("quotientMap", Call("u", F.Id("i"), F.Id("a"))))))),
                "For each i this group homomorphism composes the free-product inclusion with the quotient map "
                + "for the normal closure of relators(S)."),
            Node("standardParabolic", "Subgroups generated by factor images",
                StandardFormula(),
                "Definition 2.13 uses subgroup closure in the actual quotient. The subset J ranges over all subsets "
                + "of I. A parabolic is the image of this subgroup under conjugation by an element of the quotient."),
            Node("claim", "The universal affirmative answer",
                EqTo(F.Id("claim"), Par(ClaimBody())),
                "Question 9.4 on printed p. 47 asks “" + Question + "” Both conjugators are arbitrary elements "
                + "of Q(S), and all three factor subsets may be any subsets of I. The group and order assumptions "
                + "are those of the supplied system. Type denotes Lean Type.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("genevois-q94-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The intersection need not be parabolic"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "Take a two-element chain with empty orthogonality as in Example 2.6. Use C16 below C4. "
                    + "The element of C4 with additive coordinate j acts on C16 by multiplication by 13 to "
                    + "the power j. Write a and t for the factor images of the two generators and H for the "
                    + "upper-factor subgroup. The twist in the actual quotient makes a² commute with t², so "
                    + "t² is in both H and its conjugate by a².")),
                    Paragraph(DefinitionDsl.Text(
                    "The factor inclusions into the semidirect group with forward multiplier 5 satisfy the "
                    + "presentation and give a map from the actual quotient. Comparing the two coordinates "
                    + "of an intersection element in this group excludes odd upper exponents. The identity "
                    + "and t² realize the two even exponents in the source intersection. Its image in C4 is "
                    + "therefore exactly the subgroup with residues 0 and 2.")),
                    Paragraph(DefinitionDsl.Text(
                    "Conjugation acts trivially on the projection to C4. The image of a standard parabolic "
                    + "is the full C4 if its subset contains the upper index and is trivial otherwise. "
                    + "This rules out every parabolic as the intersection."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("genevois2505q94"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("genevois-q94-" + name.ToLowerInvariant().Replace('.', '-')),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(DefinitionDsl.Text(prose))),
            DescribeRole.Definition);

    private static readonly Formula I = F.Id("I");
    private static readonly Formula G = F.Id("G");
    private static readonly Formula S = F.Id("S");
    private static Formula OrderedIndices(Formula body) =>
        All("I", F.Id("Type"), WithInstance(Call("PartialOrder", I), body));
    private static Formula Family(Formula body) => OrderedIndices(
        All("G", Seq(I, Sp, To, Sp, F.Id("Type")),
            WithInstance(All("i", I, Call("Group", Factor(F.Id("i")))), body)));
    private static Formula System(Formula body) => Family(All("S", Call("QuandleSystem", I, G), body));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula WithInstance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula IffTo(Formula left, Formula right) => Seq(left, Sp, Iff, Sp, right);
    private static Formula HasType(Formula left, Formula type) => Seq(left, Sp, Colon, Sp, type);
    private static Formula SetBuilder(string name, Formula type, Formula predicate) => Seq(
        OpenBrace, HasType(F.Id(name), type), Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Factor(Formula i) => new Formula.Apply(G, [i]);
    private static Formula Below(Formula k) => Call("LowerIndex", k);
    private static Formula LowerAction(Formula k) => Call("LowerAction", G, k);
    private static Formula Product() => Call("Q", S);
    private static Formula FreeProduct() => Call("FreeProduct", G);
    private static Formula PowerSet() => Call("Set", I);

    private static Formula ApplyFormula()
    {
        Formula k = F.Id("k"), action = F.Id("A"), b = F.Id("b"), i = F.Id("i"), a = F.Id("a");
        return Family(All("k", I, All("A", LowerAction(k), All("b", Factor(k),
            All("i", Below(k), All("a", Factor(Call("val", i)),
                EqTo(Call("apply", action, b, i, a),
                    Par(Seq(Call("onIndex", action, b, i), Comma, Sp, Call("onFactor", action, b, i, a))))))))));
    }

    private static Formula OrderFormula()
    {
        Formula k = F.Id("k"), action = F.Id("A"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j");
        return Family(All("k", I, All("A", LowerAction(k),
            IffTo(Call("PreservesOrder", action), Par(All("b", Factor(k), All("i", Below(k), All("j", Below(k),
                IffTo(Seq(Call("onIndex", action, b, i), Sp, Leq, Sp, Call("onIndex", action, b, j)),
                    Seq(i, Sp, Leq, Sp, j))))))))));
    }

    private static Formula QuandleLawFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), action = F.Id("A"), order = F.Id("ord");
        Formula Act(Formula actor, Formula actedOn) => Call("act", action, actor, actedOn);
        var law = All("k", I, All("j", Below(k), All("i", Below(Call("val", j)),
            All("a", Factor(Call("val", i)), All("b", Factor(Call("val", j)), All("c", Factor(k),
                EqTo(Act(c, Act(b, a)), Act(Act(c, b), Act(c, a)))))))));
        return Family(All("A", Seq(Prod, Underscore, Grp(HasType(k, I)), Sp, LowerAction(k)),
            All("ord", All("k", I, Call("PreservesOrder", new Formula.Apply(action, [k]))),
                IffTo(Call("IsQuandleAction", action, order), Par(law)))));
    }

    private static Formula RelatorsFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), a = F.Id("a"), b = F.Id("b"), r = F.Id("r");
        var ai = Call("u", i, a);
        var bj = Call("u", j, b);
        Formula Relator(Formula rhs) => EqTo(r, Seq(ai, Sp, bj, Sp, Inverse(rhs)));
        var commutation = Par(Seq(Call("Orthogonal", S, i, j), Sp, Land, Sp, Relator(Seq(bj, Sp, ai))));
        var twist = Par(Seq(i, Sp, Lt, Sp, j, Sp, Land, Sp,
            Relator(Seq(bj, Sp, Call("w", S, b, i, a)))));
        var members = Ex("i", I, Ex("j", I, Ex("a", Factor(i), Ex("b", Factor(j),
            Par(Seq(commutation, Sp, Lor, Sp, twist))))));
        return System(EqTo(Call("relators", S), SetBuilder("r", FreeProduct(), members)));
    }

    private static Formula StandardFormula()
    {
        Formula j = F.Id("j"), set = F.Id("J"), q = F.Id("q"), a = F.Id("a");
        return System(All("J", PowerSet(), EqTo(Call("P", S, set),
            Call("closure", SetBuilder("q", Product(),
                Ex("j", I, Seq(j, Sp, InMacro, Sp, set, Sp, Land, Sp,
                    Par(Ex("a", Factor(j), EqTo(Call("factor", S, j, a), q))))))))));
    }

    private static Formula ClaimBody()
    {
        var left = Call("intersection", Conjugate("g", "J"), Conjugate("h", "L"));
        return System(All("J", PowerSet(), All("L", PowerSet(), All("g", Product(), All("h", Product(),
            Ex("T", PowerSet(), Ex("k", Product(), EqTo(left, Conjugate("k", "T")))))))));
    }

    private static Formula Inverse(Formula term) => Seq(Par(term), Caret, Grp(Seq(Minus, D(1))));

    private static Formula Conjugate(string conjugator, string subset)
    {
        var g = F.Id(conjugator);
        return Seq(g, Sp, Call("P", S, F.Id(subset)), Sp, Inverse(g));
    }
}

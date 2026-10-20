using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GeneralizedCHSHGroupDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/cuimehtamousavinezhadi2020chsh");
    private static readonly Formula N = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Z = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula n = F.Id("n");
    private static readonly Formula k = F.Id("k");
    private static readonly Formula i = F.Id("i");
    private static readonly Formula a = F.Id("a");
    private static readonly Formula b = F.Id("b");
    private static readonly Formula h = F.Id("H");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least two, the presented generalized CHSH group is a semidirect product of C_(2n) x C_2^(n-2) by C_n, with an explicit cyclic action.",
        H("A product decomposition of the generalized CHSH groups"),
        Blocks(
            Node("P0", "The first free generator", Equal(Call("P0"), App(Q("FreeGroup", "of"), D(0))),
                "P0 is generator 0 of FreeGroup (Fin 3), representing the paper's P_0.", AssessedProvenance.FromLiterature(Source)),
            Node("P1", "The second free generator", Equal(Call("P1"), App(Q("FreeGroup", "of"), D(1))),
                "P1 is generator 1 of FreeGroup (Fin 3), representing the paper's P_1.", AssessedProvenance.FromLiterature(Source)),
            Node("J", "The central free generator", Equal(Call("J"), App(Q("FreeGroup", "of"), D(2))),
                "J is generator 2 of FreeGroup (Fin 3), representing the paper's J.", AssessedProvenance.FromLiterature(Source)),
            Node("rels", "The relator set", RelsFormula(),
                "Section 5, printed p. 24, defines: G_n = <P_0, P_1, J | P_0^n, P_1^n, J^n, [J, P_0], [J, P_1], J^i(P_0^iP_1^(-i))^2 for 1 <= i <= floor(n/2)>. These words are equal to the identity. The index i is natural; its negated exponent is cast to the integers. Nat.div n 2 is natural division, with value floor(n/2).", AssessedProvenance.FromLiterature(Source)),
            Node("G", "The presented group", All("n", N, Equal(Call("G", n), Call("PresentedGroup", Call("rels", n)))),
                "G n is the quotient of the free group on these three generators by the normal closure of rels n, the group G_n of Section 5.", AssessedProvenance.FromLiterature(Source)),
            Node("L", "The abelian factor", All("n", N, Equal(Call("L", n),
                Seq(Cyclic(Mul(D(2), n)), Sp, Times, Sp, Parenthesized(new Formula.TypeArrow(Index(), Cyclic(D(2))))))),
                "L n is C_(2n) times n-2 independent copies of C_2. Fin (n-2) indexes the independent involutions; subtraction here is natural subtraction.", AssessedProvenance.FromRepo(Source)),
            Node("cyclicHom", "A homomorphism out of a cyclic group", CyclicHomFormula(),
                "For a^n = 1, cyclicHom sends the additive residue of an integer j to a^j. It uses the additive universal map ZMod.lift and the multiplicative type conversion. The parenthesized proposition in the subtype constructor is its constructor proof field: zmultiplesHom sends the integer n to zero.", AssessedProvenance.FromRepo(Source)),
            Node("cyclicHom_int", "Evaluation on an integer residue", CyclicHomIntFormula(),
                "For every group H, natural n, element a with a^n = 1 and integer i, cyclicHom n a ha sends ofAdd (i : ZMod n) to the integer power a^i.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("s", "The cyclic generator", All("n", N, Equal(Call("s", n), Pair(Call("ofAdd", D(1)), D(1)))),
                "The first component is 1 in ZMod (2*n), converted to multiplicative notation; the function component is constantly the identity.", AssessedProvenance.FromRepo(Source)),
            Node("t", "The independent involutions", All("n", N, All("i", Index(), Equal(Call("t", n, i),
                Pair(D(1), App(Q("Pi", "mulSingle"), i, Call("ofAdd", D(1))))))),
                "t n i has first component 1 and is 1 except for ofAdd 1 at i in its function component. The paper's one-based index is i.val+1.", AssessedProvenance.FromRepo(Source)),
            Node("liftL", "The homomorphism from the abelian factor", LiftLFormula(),
                "The images a and b i satisfy a^(2*n) = 1, (b i)^2 = 1 and commute pairwise. noncommPiCoprod forms the map from the involution factors and noncommCoprod joins it to the cyclic factor. The parenthesized propositions display the full proof arguments: images from distinct involution factors commute, and each cyclic-factor image commutes with each image of the involution product.", AssessedProvenance.FromRepo(Source)),
            Node("ts", "The product of independent involutions", All("n", N, Equal(Call("ts", n),
                Product(i, Index(), Call("t", n, i)))),
                "ts multiplies all independent involutions over Fin (n-2); the product is 1 when n = 2.", AssessedProvenance.FromRepo(Source)),
            Node("u", "The dependent last involution", UFormula(),
                "For 1 <= k <= n-2, u n k is t n at the finite index k-1. At k = n-1 outside that interval it is s n raised to n times ts n; at all other indices it is 1. The parenthesized proposition k-1 < n-2 is the Fin constructor proof field under the first branch's condition. This definition also fixes the values for n below two.", AssessedProvenance.FromRepo(Source)),
            Node("e", "The cyclic orbit coordinates", All("n", N, All("k", N,
                Equal(Call("e", n, k), Mul(Call("s", n), Call("u", n, k))))),
                "e n k is s n times the k-th extended involution. For n at least two, e n 0 = e n n = s n.", AssessedProvenance.FromRepo(Source)),
            Node("step", "One cyclic step", StepFormula(),
                "step sends s to e n 1 and each t n i to e n (i.val+2) times the inverse of e n 1. Its four parenthesized proof arguments assert order dividing 2*n for the first image, square one for each involution image, pairwise commutation of those images, and their commutation with the first image.", AssessedProvenance.FromRepo(Source)),
            Node("stepAut", "The cyclic automorphism", StepAutFormula(),
                "For n at least two, step iterated n times is the identity on L n. stepAut has forward function step n and inverse function the (n-1)-fold iterate of step n. The parenthesized propositions are constructor proof fields: the two Equiv.mk fields assert the inverse identities for every x in L n, and the MulEquiv.mk field asserts preservation of multiplication for every x and y in L n.", AssessedProvenance.FromRepo(Source)),
            Node("alpha", "The action of C_n", AlphaFormula(),
                "For n at least two, alpha maps ofAdd 1 to stepAut n. Thus alpha(s) = s times u n 1 and alpha(t n i) = u n (i.val+2) times u n 1. The dependent last involution gives the wrap-around. The parenthesized proof argument asserts that stepAut n hn raised to n is the identity automorphism under the branch hypothesis hn. For n below two, alpha is the constant identity homomorphism.", AssessedProvenance.FromRepo(Source)),
            Node("claim", "The uniform decomposition", ClaimFormula(),
                "Section 1.4 (Further work), item 2, printed p. 7: \"In Section 5, we give efficient explicit presentations for G_n and its multiplication table. Can we go further and characterize these groups in terms of direct and semidirect products of small well-known groups? The first few cases are as follows\" The encoding answers this question for every natural n >= 2 by an actual multiplicative equivalence. C_m is Multiplicative (ZMod m); the elementary abelian factor uses Fin (n-2), and alpha is the displayed action.", AssessedProvenance.FromRepo(Source)),
            Node("result", "The decomposition theorem", ClaimBodyFormula(),
                "The forward homomorphism sends P0 to inr(ofAdd 1), P1 to inl(s) times inr(ofAdd 1), and J to inl(s^2). In the presented group, the elements P0^i P1^(-i) commute, allowing the inverse map from L. Its compatibility with conjugation by P0 gives a homomorphism from the semidirect product. Both composites fix the generators, so the maps form a multiplicative equivalence. No group-order computation is used.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cui-mehta-mousavi-nezhadi-2020-chsh-group-decomposition"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("cmmn-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => arguments.Length == 0 ? Named(name) : App(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Constructor(Formula left, Formula right) => Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Inverse(Formula value) => Pow(value, Seq(Minus, D(1)));
    private static Formula Cyclic(Formula modulus) => Call("Multiplicative", Call("ZMod", modulus));
    private static Formula Index() => Call("Fin", Sub(n, D(2)));
    private static Formula GroupBind(Formula body) => All("H", Named("Type"),
        Seq(OpenBracket, Call("Group", h), CloseBracket, Comma, Sp, body));
    private static Formula Function(Formula variable, Formula domain, Formula body) =>
        Seq(Named("fun"), Sp, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body);
    private static Formula Product(Formula variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(variable, InMacro, Sp, domain)), Sp, body);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);

    private static Formula RelsFormula()
    {
        Formula p = Call("P0"), q = Call("P1"), j = Call("J"), r = F.Id("r");
        Formula words = new Formula.SetLiteral([Pow(p, n), Pow(q, n), Pow(j, n),
            Call("commutatorElement", j, p), Call("commutatorElement", j, q)]);
        Formula cast = Parenthesized(Seq(i, Colon, Sp, Z));
        Formula relation = Equal(r, Mul(Pow(j, i), Pow(Mul(Pow(p, i), Pow(q, Seq(Minus, cast))), D(2))));
        Formula set = Seq(OpenBrace, r, Colon, Sp, Call("FreeGroup", Call("Fin", D(3))), Sp, Mid, Sp, Some("i", N,
            And(LeqTo(D(1), i), And(LeqTo(i, App(Q("Nat", "div"), n, D(2))), relation))), CloseBrace);
        return All("n", N, Equal(Call("rels", n), Seq(words, Sp, Cup, Sp, set)));
    }

    private static Formula CyclicHomFormula()
    {
        Formula ha = F.Id("ha");
        Formula multiples = Call("zmultiplesHom", Call("Additive", h), App(Q("Additive", "ofMul"), a));
        Formula annihilates = Equal(App(multiples, Parenthesized(Seq(n, Colon, Sp, Z))), D(0));
        Formula lifted = App(Q("ZMod", "lift"), n,
            Constructor(multiples, Parenthesized(annihilates)));
        return GroupBind(All("n", N, All("a", h, All("ha", Equal(Pow(a, n), D(1)),
            Equal(Call("cyclicHom", n, a, ha), App(Q("AddMonoidHom", "toMultiplicativeLeft"), lifted))))));
    }

    private static Formula CyclicHomIntFormula()
    {
        Formula ha = F.Id("ha");
        Formula residue = Call("ofAdd", Parenthesized(Seq(i, Colon, Sp, Call("ZMod", n))));
        return GroupBind(All("n", N, All("a", h, All("ha", Equal(Pow(a, n), D(1)),
            All("i", Z, Equal(Call("cyclicHom", n, a, ha, residue), Pow(a, i)))))));
    }

    private static Formula LiftLFormula()
    {
        Formula ha = F.Id("ha"), hb = F.Id("hb"), hc = F.Id("hc"), hd = F.Id("hd"), j = F.Id("j");
        Formula x = F.Id("x"), y = F.Id("y");
        Formula images = Function(i, Index(), Call("cyclicHom", D(2), App(b, i), App(hb, i)));
        Formula imageCommutes = All("i", Index(), All("j", Index(),
            new Formula.Logic(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j),
                FormulaLogicOperator.Implies, All("x", Cyclic(D(2)), All("y", Cyclic(D(2)),
                    Call("Commute", App(Call("cyclicHom", D(2), App(b, i), App(hb, i)), x),
                        App(Call("cyclicHom", D(2), App(b, j), App(hb, j)), y)))))));
        Formula piMap = App(Q("MonoidHom", "noncommPiCoprod"), images, Parenthesized(imageCommutes));
        Formula cyclicMap = Call("cyclicHom", Mul(D(2), n), a, ha);
        Formula factorsCommute = All("x", Cyclic(Mul(D(2), n)),
            All("y", new Formula.TypeArrow(Index(), Cyclic(D(2))),
                Call("Commute", App(cyclicMap, x), App(piMap, y))));
        Formula rhs = App(Q("MonoidHom", "noncommCoprod"), cyclicMap, piMap, Parenthesized(factorsCommute));
        return GroupBind(All("n", N, All("a", h, All("b", new Formula.TypeArrow(Index(), h),
            All("ha", Equal(Pow(a, Mul(D(2), n)), D(1)),
            All("hb", All("i", Index(), Equal(Pow(App(b, i), D(2)), D(1))),
            All("hc", All("i", Index(), All("j", Index(), Call("Commute", App(b, i), App(b, j)))),
            All("hd", All("i", Index(), Call("Commute", a, App(b, i))),
                Equal(Call("liftL", n, a, b, ha, hb, hc, hd), rhs)))))))));
    }

    private static Formula UFormula()
    {
        Formula bounds = And(LeqTo(D(1), k), LeqTo(k, Sub(n, D(2))));
        Formula indexBound = new Formula.Relation(Sub(k, D(1)), FormulaRelationOperator.LessThan, Sub(n, D(2)));
        Formula rhs = Conditional(bounds, Call("t", n, Constructor(Sub(k, D(1)), Parenthesized(indexBound))),
            Conditional(Equal(k, Sub(n, D(1))), Mul(Pow(Call("s", n), n), Call("ts", n)), D(1)));
        return All("n", N, All("k", N, Equal(Call("u", n, k), rhs)));
    }

    private static Formula StepFormula()
    {
        Formula j = F.Id("j");
        Formula image = Function(i, Index(), Mul(Call("e", n, Add(Call("val", i), D(2))), Inverse(Call("e", n, D(1)))));
        Formula firstOrder = Equal(Pow(Call("e", n, D(1)), Mul(D(2), n)), D(1));
        Formula imageI = Mul(Call("e", n, Add(Call("val", i), D(2))), Inverse(Call("e", n, D(1))));
        Formula imageJ = Mul(Call("e", n, Add(Call("val", j), D(2))), Inverse(Call("e", n, D(1))));
        Formula imageSquare = All("i", Index(), Equal(Pow(imageI, D(2)), D(1)));
        Formula imagesCommute = All("i", Index(), All("j", Index(), Call("Commute", imageI, imageJ)));
        Formula firstCommutes = All("i", Index(), Call("Commute", Call("e", n, D(1)), imageI));
        return All("n", N, Equal(Call("step", n), Call("liftL", n, Call("e", n, D(1)), image,
            Parenthesized(firstOrder), Parenthesized(imageSquare), Parenthesized(imagesCommute), Parenthesized(firstCommutes))));
    }

    private static Formula StepAutFormula()
    {
        Formula hn = F.Id("hn");
        Formula x = F.Id("x"), y = F.Id("y"), domain = Call("L", n);
        Formula inverse = new Formula.Power(Call("step", n), Seq(OpenBracket, Sub(n, D(1)), CloseBracket));
        Formula leftInverse = All("x", domain, Equal(App(inverse, App(Call("step", n), x)), x));
        Formula rightInverse = All("x", domain, Equal(App(Call("step", n), App(inverse, x)), x));
        Formula preservesMul = All("x", domain, All("y", domain,
            Equal(App(Call("step", n), Mul(x, y)), Mul(App(Call("step", n), x), App(Call("step", n), y)))));
        Formula rhs = App(Q("MulEquiv", "mk"),
            App(Q("Equiv", "mk"), Call("step", n), inverse, Parenthesized(leftInverse), Parenthesized(rightInverse)),
            Parenthesized(preservesMul));
        return All("n", N, All("hn", LeqTo(D(2), n), Equal(Call("stepAut", n, hn), rhs)));
    }

    private static Formula AlphaFormula() => All("n", N, Equal(Call("alpha", n),
        Seq(Named("if"), Sp, F.Id("hn"), Colon, Sp, LeqTo(D(2), n), Sp, Named("then"), Sp,
            Call("cyclicHom", n, Call("stepAut", n, F.Id("hn")),
                Parenthesized(Equal(Pow(Call("stepAut", n, F.Id("hn")), n), D(1)))), Sp, Named("else"), Sp, D(1))));

    private static Formula ClaimFormula() =>
        new Formula.Logic(Call("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBodyFormula()));

    private static Formula ClaimBodyFormula()
    {
        Formula product = Call("SemidirectProduct", Call("L", n), Cyclic(n), Call("alpha", n));
        Formula equivalence = Call("MulEquiv", Call("G", n), product);
        return All("n", N,
            new Formula.Logic(LeqTo(D(2), n), FormulaLogicOperator.Implies, Call("Nonempty", equivalence)));
    }
}

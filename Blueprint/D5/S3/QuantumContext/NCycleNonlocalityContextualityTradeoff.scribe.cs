using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class NCycleNonlocalityContextualityTradeoffDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Observer/portoetal2024tradeoffnonlocalitycontextuality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Bell and contextuality inequalities satisfy the trade-off for every binary n-cycle.",
        H("The nonlocality–contextuality trade-off on a binary cycle"),
        Blocks(
            Definition("behavior", "Joint probability tables", "Behavior", BehaviorFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A behavior is a real table indexed by Alice's setting x in Fin 2, Bob's cyclic context i "
                    + "in Fin n, Alice's outcome a and Bob's ordered outcomes b,c in Bool. The context "
                    + "contains measurements i and finRotate n i. Boolean outcomes label the two signs "
                    + "of the source's binary scenario (final_version.tex, lines 181–196 and 225). "
                    + "The type alone imposes no positivity or normalization."),
            Definition("bob-behavior", "Bob's context tables", "BobBehavior", BobBehaviorFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Bob's table assigns a real number to each context i and pair of Boolean outcomes b,c. "
                    + "The two outcomes belong to consecutive measurements of the cycle "
                    + "(final_version.tex, lines 181–196 and 225)."),
            Definition("alice-response", "Alice's response tables", "AliceResponse", AliceResponseFormula(),
                AssessedProvenance.FromLiterature(Source),
                "An Alice response is a real table on her two settings and two outcomes. Such responses "
                    + "are the Alice factors in the generalized-local decomposition "
                    + "(final_version.tex, lines 213–219 and 225)."),
            Definition("is-nd", "Nondisturbing cycle probabilities", "IsND", IsNDFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Each context has a nonnegative probability distribution. Summing over the first outcome "
                    + "in context i gives the same distribution for the shared measurement as summing "
                    + "over the second outcome in the next context. This is nondisturbance on the "
                    + "cycle (final_version.tex, lines 144–149 and 225)."),
            Definition("is-nsnd", "Nonsignaling and nondisturbing joint probabilities", "IsNSND",
                IsNSNDFormula(), AssessedProvenance.FromLiterature(Source),
                "The five conditions are nonnegativity, normalization for each setting and context, "
                    + "agreement of the joint Alice/shared-Bob marginal in consecutive contexts, "
                    + "independence of Bob's context marginal from Alice's setting, and independence "
                    + "of Alice's marginal from Bob's context. They specialize the source's NSND "
                    + "conditions to the binary cycle (final_version.tex, lines 181–196 and 225)."),
            Definition("bob-marginal", "The Bob marginal at setting zero", "bobMarginal",
                BobMarginalFormula(), AssessedProvenance.FromLiterature(Source),
                "Sum over Alice's outcome at setting zero. For an NSND table the result is independent "
                    + "of which Alice setting is used (final_version.tex, lines 187–196)."),
            Definition("product-behavior", "Independent product probabilities", "productBehavior",
                ProductBehaviorFormula(), AssessedProvenance.FromLiterature(Source),
                "Multiply Alice's response probability by Bob's context probability. These independent "
                    + "products are the terms mixed in generalized locality "
                    + "(final_version.tex, lines 213–219)."),
            Definition("deterministic", "Tables from a global outcome assignment", "deterministic",
                DeterministicFormula(), AssessedProvenance.FromLiterature(Source),
                "A global Boolean assignment s gives probability one to its ordered pair of outcomes "
                    + "in each context and zero to every other pair. These are the deterministic "
                    + "noncontextual behaviors (final_version.tex, lines 151–159 and 225). The curried "
                    + "table applies the repository's deterministic postprocessing kernel to ordered outcome pairs."),
            Definition("is-generalized-local", "Generalized-local joint tables", "IsGeneralizedLocal",
                IsGeneralizedLocalFormula(), AssessedProvenance.FromLiterature(Source),
                "Alice responses satisfy the row-stochastic predicate: nonnegative entries and row sum one. "
                    + "Take the real convex hull of independent products of such a response for Alice "
                    + "and a nondisturbing behavior for Bob. Bob's hidden response may itself be "
                    + "contextual, as allowed in the generalized-local definition "
                    + "(final_version.tex, lines 213–219)."),
            Definition("is-noncontextual", "Noncontextual Bob tables", "IsNoncontextual",
                IsNoncontextualFormula(), AssessedProvenance.FromLiterature(Source),
                "A Bob table is noncontextual when it is a finite convex combination of context tables "
                    + "from global deterministic assignments (final_version.tex, lines 151–159)."),
            Definition("is-normalized-gbell", "Normalized affine Bell inequalities", "IsNormalizedGBell",
                IsNormalizedGBellFormula(), AssessedProvenance.FromLiterature(Source),
                "The pair f consists of a real linear functional and a real offset. Its affine value "
                    + "is nonpositive on every generalized-local table, is at most one on every NSND "
                    + "table, and equals one on some NSND table. Thus the maximum is attained, "
                    + "as required by the source's normalization (final_version.tex, line 276)."),
            Definition("is-normalized-nc", "Normalized affine contextuality inequalities", "IsNormalizedNC",
                IsNormalizedNCFormula(), AssessedProvenance.FromLiterature(Source),
                "The pair t consists of a real linear functional on Bob tables and a real offset. "
                    + "Its affine value is nonpositive on every noncontextual table and has attained "
                    + "maximum one over Bob marginals of NSND tables "
                    + "(final_version.tex, line 276)."),
            Definition("claim", "The trade-off for every cycle length at least three", "claim",
                Equivalence(Local("claim"), ClaimBody()), AssessedProvenance.FromRepo(Source),
                "For every natural n at least three, every pair of normalized affine inequalities f,t "
                    + "and every NSND table p, the Bell value at p plus the contextuality value at its "
                    + "Bob marginal is at most one. This is the binary two-setting reading of the "
                    + "all-cycle conjecture (final_version.tex, lines 373–375), with the inequality "
                    + "of lines 279–286 and the scenario of line 225."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The normalized trade-off holds for every binary cycle"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Summing an NSND table over Alice gives a nondisturbing Bob table. Conversely, "
                            + "the independent product of any probability response for Alice with any "
                            + "nondisturbing Bob table is NSND: the normalizations factor, the shared "
                            + "marginals agree, and each party's marginal is independent of the other "
                            + "party's choice.")),
                    Paragraph(Text(
                        "For a Boolean edge pattern γ, let Vγ assign probability one half when b xor c "
                            + "equals γ(i), and zero otherwise. Every such table is nondisturbing. "
                            + "The product of the edge signs, taking sign −1 at true and +1 at false, "
                            + "is determined by the Boolean sum of γ: apply Mathlib's map_sum to "
                            + "the additive map into multiplicative real signs, using the repository's boolSign. "
                            + "The parity table itself uses the existing parityBox scalar law. "
                            + "If that sum is false, prefix "
                            + "Boolean sums, using Mathlib's Iio_insert identity for the prefix sets, "
                            + "construct a global assignment s whose consecutive xor "
                            + "values are γ. The wraparound edge follows from the total sum being "
                            + "false. Then Vγ is the equal mixture of the deterministic assignments "
                            + "s and its pointwise complement, so it is noncontextual.")),
                    Paragraph(Text(
                        "Apply the cyclic circulation decomposition to a nondisturbing table. It lies "
                            + "in the convex hull of deterministic tables and all the tables Vγ. "
                            + "Replace each even-parity Vγ by its noncontextual deterministic mixture. "
                            + "This leaves deterministic tables and odd-parity Vγ as sufficient "
                            + "generating tables. For two distinct odd patterns γ,η, choose a position "
                            + "where they differ and flip that bit in both patterns. The resulting "
                            + "patterns are even by Mathlib's sum_eq_sum_iff_single criterion: "
                            + "only the flipped summand changes. Their two V tables have the same midpoint as the "
                            + "original pair: away from the chosen position nothing changes, and at "
                            + "that position the opposite parities still average equally. The midpoint "
                            + "is consequently noncontextual. The source also gives the midpoint "
                            + "property in final_version.tex, lines 521–532.")),
                    Paragraph(Text(
                        "Write T(r) = t.1(r) + t.2. A uniform Alice response turns every Vγ into the "
                            + "Bob marginal of an NSND product, so normalization gives T(Vγ) ≤ 1. "
                            + "Some odd-pattern Vγ must attain one. Otherwise every deterministic "
                            + "table and every odd-pattern V table lies in the strict affine "
                            + "half-space T < 1, which is convex. Their convex hull would then contain "
                            + "no Bob marginal attaining the required maximum. Fix a maximizing "
                            + "pattern γ. For every other odd η, noncontextuality of the midpoint "
                            + "gives (T(Vη) + T(Vγ))/2 ≤ 0 and hence T(Vη) ≤ 0.")),
                    Paragraph(Text(
                        "In a finite convex decomposition of a nondisturbing table r, collect the "
                            + "weights of all terms equal to Vγ into v. All other terms have "
                            + "nonpositive T value, so T(r) ≤ v. Nonnegativity of every generating "
                            + "table also gives v Vγ(i,b,c) ≤ r(i,b,c) at every coordinate.")),
                    Paragraph(Text(
                        "For each Alice setting x and outcome a, take the subnormalized Bob table "
                            + "q(i,b,c) = p(x,i,a,b,c). Its mass m is independent of i. If m is zero, "
                            + "nonnegativity forces the whole slice to vanish. If m is positive, "
                            + "divide by m to obtain a nondisturbing table and apply the preceding "
                            + "weight bound. Multiplying back by m gives a nonnegative weight w(x,a) "
                            + "with t.1(q) + m t.2 ≤ w(x,a) and w(x,a) Vγ ≤ q.")),
                    Paragraph(Text(
                        "Put c = T(bobMarginal p) and suppose c > 0. Summing the slice inequalities "
                            + "over a gives c ≤ W(x), where W(x) is the sum of w(x,a). This uses "
                            + "Bob's independence from x and normalization of p. Each W(x) is "
                            + "positive, so α(x,a) = w(x,a)/W(x) is a probability response. Since "
                            + "c α(x,a) ≤ w(x,a), the independent product L(x,i,a,b,c′) = "
                            + "α(x,a)Vγ(i,b,c′) satisfies c L ≤ p coordinatewise. This L is both "
                            + "generalized-local and NSND.")),
                    Paragraph(Text(
                        "For any NSND generalized-local L with c L ≤ p and 0 < c ≤ 1, the affine "
                            + "Bell value F(p) = f.1(p) + f.2 is at most 1 − c. If c = 1, equal "
                            + "total masses and coordinatewise domination force L = p, and locality "
                            + "gives F(p) ≤ 0. If c < 1, set R = (p − c L)/(1 − c). Domination "
                            + "makes R nonnegative, and the linear normalization and marginal "
                            + "identities show that R is NSND. The identity p = c L + (1 − c) R "
                            + "and affinity give F(p) = c F(L) + (1 − c) F(R) ≤ 1 − c.")),
                    Paragraph(Text(
                        "Finally, fix n ≥ 3, normalized f,t and an NSND p. If T(bobMarginal p) ≤ 0, "
                            + "the bound F(p) ≤ 1 immediately proves the sum bound. Otherwise the "
                            + "maximizing odd pattern and the slice construction give the product L "
                            + "above. Normalization of t gives c ≤ 1, so the dominated-product "
                            + "argument yields F(p) ≤ 1 − c. Adding c proves the stated inequality. "
                            + "The statement concerns binary cyclic NSND probability tables with "
                            + "two Alice settings; it assumes no quantum realization."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("porto-et-al-2024-n-cycle-nonlocality-contextuality-tradeoff"),
                    ResolutionKind.Proved)))));

    private static Formula BehaviorFormula() => All("n", Naturals(), Equal(
        Typed(LocalCall("Behavior", X("n")), X("Type")),
        Arrow(Fin(D(2)), Arrow(Fin(X("n")), Arrow(BoolType(),
            Arrow(BoolType(), Arrow(BoolType(), Reals())))))));

    private static Formula BobBehaviorFormula() => All("n", Naturals(), Equal(
        Typed(LocalCall("BobBehavior", X("n")), X("Type")), BobTable()));

    private static Formula AliceResponseFormula() => Equal(
        Typed(Local("AliceResponse"), X("Type")), Arrow(Fin(D(2)), Arrow(BoolType(), Reals())));

    private static Formula IsNDFormula()
    {
        Formula positive = All("i", Fin(X("n")), All("b", BoolType(), All("c", BoolType(),
            LE(Real(0), At(X("r"), X("i"), X("b"), X("c"))))));
        Formula normalized = All("i", Fin(X("n")), Equal(
            SumOf("b", SumOf("c", At(X("r"), X("i"), X("b"), X("c")))), Real(1)));
        Formula consistent = All("i", Fin(X("n")), All("c", BoolType(), Equal(
            SumOf("b", At(X("r"), X("i"), X("b"), X("c"))),
            SumOf("d", At(X("r"), Rotate(X("i")), X("c"), X("d"))))));
        return All("n", Naturals(), All("r", Bob(), Equivalence(LocalCall("IsND", X("r")),
            And(positive, And(normalized, consistent)))));
    }

    private static Formula IsNSNDFormula()
    {
        Formula positive = All("x", Fin(D(2)), All("i", Fin(X("n")),
            All("a", BoolType(), All("b", BoolType(), All("c", BoolType(),
                LE(Real(0), P("x", X("i"), "a", "b", "c")))))));
        Formula normalized = All("x", Fin(D(2)), All("i", Fin(X("n")), Equal(
            SumOf("a", SumOf("b", SumOf("c", P("x", X("i"), "a", "b", "c")))), Real(1))));
        Formula shared = All("x", Fin(D(2)), All("i", Fin(X("n")),
            All("a", BoolType(), All("c", BoolType(), Equal(
                SumOf("b", P("x", X("i"), "a", "b", "c")),
                SumOf("d", P("x", Rotate(X("i")), "a", "c", "d")))))));
        Formula bob = All("x", Fin(D(2)), All("y", Fin(D(2)), All("i", Fin(X("n")),
            All("b", BoolType(), All("c", BoolType(), Equal(
                SumOf("a", P("x", X("i"), "a", "b", "c")),
                SumOf("a", P("y", X("i"), "a", "b", "c"))))))));
        Formula alice = All("x", Fin(D(2)), All("i", Fin(X("n")), All("j", Fin(X("n")),
            All("a", BoolType(), Equal(
                SumOf("b", SumOf("c", P("x", X("i"), "a", "b", "c"))),
                SumOf("b", SumOf("c", P("x", X("j"), "a", "b", "c"))))))));
        return All("n", Naturals(), All("p", Joint(), Equivalence(LocalCall("IsNSND", X("p")),
            And(positive, And(normalized, And(shared, And(bob, alice)))))));
    }

    private static Formula BobMarginalFormula()
    {
        Formula body = LambdaOf("i", Fin(X("n")), LambdaOf("b", BoolType(), LambdaOf("c", BoolType(),
            SumOf("a", At(X("p"), Typed(D(0), Fin(D(2))), X("i"), X("a"), X("b"), X("c"))))));
        return All("n", Naturals(), All("p", Joint(), Equal(
            Typed(LocalCall("bobMarginal", X("p")), Bob()), body)));
    }

    private static Formula ProductBehaviorFormula()
    {
        Formula body = LambdaOf("x", Fin(D(2)), LambdaOf("i", Fin(X("n")),
            LambdaOf("a", BoolType(), LambdaOf("b", BoolType(), LambdaOf("c", BoolType(),
                Mul(At(X("α"), X("x"), X("a")), At(X("r"), X("i"), X("b"), X("c"))))))));
        return All("n", Naturals(), All("α", Alice(), All("r", Bob(), Equal(
            Typed(LocalCall("productBehavior", X("α"), X("r")), Joint()), body))));
    }

    private static Formula DeterministicFormula()
    {
        Formula condition = And(Equal(At(X("s"), X("i")), X("b")),
            Equal(At(X("s"), Rotate(X("i"))), X("c")));
        Formula body = LambdaOf("i", Fin(X("n")), LambdaOf("b", BoolType(), LambdaOf("c", BoolType(),
            At(Qualified("ite"), condition, Real(1), Real(0)))));
        return All("n", Naturals(), All("s", Arrow(Fin(X("n")), BoolType()), Equal(
            Typed(LocalCall("deterministic", X("s")), Bob()), body)));
    }

    private static Formula IsGeneralizedLocalFormula()
    {
        Formula products = SetOf("q", Joint(), Some("α", Alice(), Some("r", Bob(),
            And(At(Qualified("D5", "S3", "Estimation", "DecisionRisk",
                "DescentDefectBounds", "IsRowStochastic"), X("α")), And(LocalCall("IsND", X("r")),
                Equal(X("q"), LocalCall("productBehavior", X("α"), X("r"))))))));
        return All("n", Naturals(), All("p", Joint(), Equivalence(
            LocalCall("IsGeneralizedLocal", X("p")),
            Member(X("p"), At(Qualified("convexHull"), Reals(), products)))));
    }

    private static Formula IsNoncontextualFormula()
    {
        Formula assignments = At(Qualified("Set", "range"), Typed(Local("deterministic"),
            Arrow(Arrow(Fin(X("n")), BoolType()), Bob())));
        return All("n", Naturals(), All("r", Bob(), Equivalence(LocalCall("IsNoncontextual", X("r")),
            Member(X("r"), At(Qualified("convexHull"), Reals(), assignments)))));
    }

    private static Formula IsNormalizedGBellFormula()
    {
        Formula local = All("p", Joint(), Imp(LocalCall("IsGeneralizedLocal", X("p")),
            LE(Affine(X("f"), X("p")), Real(0))));
        Formula upper = All("p", Joint(), Imp(LocalCall("IsNSND", X("p")),
            LE(Affine(X("f"), X("p")), Real(1))));
        Formula attained = Some("p", Joint(), And(LocalCall("IsNSND", X("p")),
            Equal(Affine(X("f"), X("p")), Real(1))));
        return All("n", Naturals(), All("f", AffineType(Joint()), Equivalence(
            LocalCall("IsNormalizedGBell", X("f")), And(local, And(upper, attained)))));
    }

    private static Formula IsNormalizedNCFormula()
    {
        Formula local = All("r", Bob(), Imp(LocalCall("IsNoncontextual", X("r")),
            LE(Affine(X("t"), X("r")), Real(0))));
        Formula upper = All("p", Joint(), Imp(LocalCall("IsNSND", X("p")),
            LE(Affine(X("t"), LocalCall("bobMarginal", X("p"))), Real(1))));
        Formula attained = Some("p", Joint(), And(LocalCall("IsNSND", X("p")),
            Equal(Affine(X("t"), LocalCall("bobMarginal", X("p"))), Real(1))));
        return All("n", Naturals(), All("t", AffineType(Bob()), Equivalence(
            LocalCall("IsNormalizedNC", X("t")), And(local, And(upper, attained)))));
    }

    private static Formula ClaimBody()
    {
        Formula inequality = LE(Add(Affine(X("f"), X("p")),
            Affine(X("t"), LocalCall("bobMarginal", X("p")))), Real(1));
        return All("n", Naturals(), Imp(LE(Typed(D(3), Naturals()), X("n")),
            All("f", AffineType(Joint()), All("t", AffineType(Bob()),
                Imp(LocalCall("IsNormalizedGBell", X("f")), Imp(LocalCall("IsNormalizedNC", X("t")),
                    All("p", Joint(), Imp(LocalCall("IsNSND", X("p")), inequality))))))));
    }

    private static DocumentBlock Definition(string id, string title, string declaration,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => name == "α" ? Alpha : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "QuantumContext",
        "NCycleNonlocalityContextualityTradeoff", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Real(byte value) => Typed(D(value), Reals());
    private static Formula BoolType() => Qualified("Bool");
    private static Formula Fin(Formula n) => At(Qualified("Fin"), n);
    private static Formula Joint() => LocalCall("Behavior", X("n"));
    private static Formula Bob() => LocalCall("BobBehavior", X("n"));
    private static Formula Alice() => Local("AliceResponse");
    private static Formula BobTable() => Arrow(Fin(X("n")), Arrow(BoolType(), Arrow(BoolType(), Reals())));
    private static Formula AffineType(Formula domain) =>
        Seq(Parenthesized(At(Qualified("LinearMap"), At(Qualified("RingHom", "id"), Reals()),
            domain, Reals())), Sp, Times, Sp, Reals());
    private static Formula Rotate(Formula i) => At(At(Qualified("Equiv", "toFun"),
        At(Qualified("finRotate"), X("n"))), i);
    private static Formula Affine(Formula f, Formula p) => Add(
        At(At(Qualified("DFunLike", "coe"), At(Qualified("Prod", "fst"), f)), p),
        At(Qualified("Prod", "snd"), f));
    private static Formula P(string x, Formula i, string a, string b, string c) =>
        At(X("p"), X(x), i, X(a), X(b), X(c));
    private static Formula SumOf(string name, Formula body) => At(Qualified("Finset", "sum"),
        Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), BoolType())),
        LambdaOf(name, BoolType(), body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, Typed(X(name), type), Sp, Mid, Sp, Parenthesized(condition), CloseBrace);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
